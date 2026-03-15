/**
 * Three-phase assembler for sim8 ISA v2: preprocessing (@include) + two-pass assembly.
 * Port of pysim8/src/pysim8/asm/parser.py + codegen.py (preprocess.py pending)
 * Single ES module, zero DOM dependency.
 */

import {
    Op,
    OpType,
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    REGISTERS,
    MNEMONICS,
    MNEMONICS_FP,
    FP_CONTROL_MNEMONICS,
    MNEMONIC_ALIASES,
    GPR_CODES,
    STACK_CODES,
    FP_REGISTERS,
    FORBIDDEN_FP_LABEL_NAMES,
    FP_SUFFIX_TO_FMT,
    FP_FMT_WIDTH,
    FP_WIDTH_REGS,
    FP_FMT_F,
    FP_FMT_O3,
    FP_FMT_N1,
    FP_FMT_N2,
    FP_DB_SUFFIX_TO_FMT,
    encodeRegaddr,
    encodeFpm,
} from "./isa.js";

import { floatToBytes } from "./fp.js";

// ── Error ────────────────────────────────────────────────────────

export class AsmError extends Error {
    constructor(message, line, filename = null) {
        super(message);
        this.line = line;
        this.filename = filename;
    }

    toString() {
        const loc = this.filename ? `${this.filename}:${this.line}` : `Line ${this.line}`;
        return `${loc}: ${this.message}`;
    }
}

// ── Cached combined mnemonic set (v2) ────────────────────────────

const ALL_MNEMONICS_V2 = new Set([...MNEMONICS, ...MNEMONICS_FP]);

// ── Operand tags ─────────────────────────────────────────────────

const TAG_REG = "reg";
const TAG_CONST = "const";
const TAG_ADDR = "addr";
const TAG_REGADDR = "regaddr";
const TAG_STRING = "string";
const TAG_LABEL = "label";
const TAG_ADDR_LABEL = "addr_label";
const TAG_FP_REG = "fp_reg";
const TAG_FLOAT = "float";
const TAG_FP_IMM = "fp_imm";

// ── Number parsing ───────────────────────────────────────────────

const _RE_HEX = /^0x([0-9A-Fa-f]+)$/;
const _RE_OCT = /^0o([0-7]+)$/;
const _RE_BIN = /^([01]+)b$/;
const _RE_DEC_EXPLICIT = /^(\d+)d$/;
const _RE_DEC = /^(\d+)$/;
const _RE_CHAR = /^'(.)'$/;
const _RE_CHAR_MULTI = /^'(.{2,})'$/;

const _NUM_FORMATS = [
    [_RE_HEX, 16],
    [_RE_OCT, 8],
    [_RE_BIN, 2],
    [_RE_DEC_EXPLICIT, 10],
    [_RE_DEC, 10],
];

function _tryParseNumber(token) {
    let m = _RE_CHAR_MULTI.exec(token);
    if (m) return null;
    m = _RE_CHAR.exec(token);
    if (m) return m[1].charCodeAt(0);
    for (const [pattern, base] of _NUM_FORMATS) {
        m = pattern.exec(token);
        if (m) return parseInt(m[1], base);
    }
    return null;
}

function _parseNumber(token, line) {
    if (_RE_CHAR_MULTI.test(token)) {
        throw new AsmError("Only one character is allowed", line);
    }
    const val = _tryParseNumber(token);
    if (val === null) {
        throw new AsmError("Invalid number format", line);
    }
    return val;
}

function _checkByteRange(value, line) {
    if (value < 0 || value > 255) {
        throw new AsmError(`${value} must have a value between 0-255`, line);
    }
    return value;
}

// ── @include regex + URL helpers ─────────────────────────────────

const _RE_INCLUDE_FULL = /^\s*@include\s+"([^"]+)"\s*$/i;
const _RE_INCLUDE_START = /^\s*@include\b/i;

function _isUrl(path) {
    return path.startsWith("http://") || path.startsWith("https://");
}

function _decodeUtf8(bytes) {
    if (bytes.includes(0)) return null;
    try {
        return new TextDecoder("utf-8", { fatal: true }).decode(bytes);
    } catch {
        return null;
    }
}

// ── Label regex ──────────────────────────────────────────────────

const _RE_LABEL = /^[.A-Za-z]\w*$/;

// ── Float literal parsing ────────────────────────────────────────

const _RE_FLOAT = /^([+-]?)(\d+\.\d*|\.\d+)([eE][+-]?\d+)?(_\w+)?$/;
const _RE_FLOAT_SPECIAL = /^([+-]?)(inf|nan)(_\w+)?$/i;

// ── Bracket operand parsing ──────────────────────────────────────

const _RE_BRACKET = /^\[(.+)\]$/;
const _RE_REG_OFFSET = /^([A-Za-z]+)\s*([+-])\s*(\d+)$/;
const _RE_REG_ONLY = /^([A-Za-z]+)$/;

function _parseBracketOperand(inner, line) {
    inner = inner.trim();

    // [reg+-offset]
    let m = _RE_REG_OFFSET.exec(inner);
    if (m) {
        const regName = m[1].toUpperCase();
        const sign = m[2];
        let offsetVal = parseInt(m[3], 10);
        if (sign === "-") offsetVal = -offsetVal;
        if (!(regName in REGISTERS)) {
            throw new AsmError(`Invalid register in address: ${m[1]}`, line);
        }
        if (offsetVal < -16 || offsetVal > 15) {
            throw new AsmError("offset must be a value between -16...+15", line);
        }
        return { tag: TAG_REGADDR, regCode: REGISTERS[regName], offset: offsetVal };
    }

    // [reg]
    m = _RE_REG_ONLY.exec(inner);
    if (m) {
        const regName = m[1].toUpperCase();
        if (regName in REGISTERS) {
            return { tag: TAG_REGADDR, regCode: REGISTERS[regName], offset: 0 };
        }
    }

    // [number]
    const val = _tryParseNumber(inner);
    if (val !== null) {
        _checkByteRange(val, line);
        return { tag: TAG_ADDR, value: val };
    }

    // [label]
    if (_RE_LABEL.test(inner)) {
        return { tag: TAG_ADDR_LABEL, name: inner.toLowerCase() };
    }

    throw new AsmError(`Invalid address: ${inner}`, line);
}

// ── Operand parsers ──────────────────────────────────────────────

function _tryBracket(token, line) {
    const m = _RE_BRACKET.exec(token);
    if (m) return _parseBracketOperand(m[1], line);
    return null;
}

function _tryRegister(token, _line) {
    const up = token.toUpperCase();
    if (up in REGISTERS) {
        return { tag: TAG_REG, code: REGISTERS[up] };
    }
    if (up in FP_REGISTERS) {
        const r = FP_REGISTERS[up];
        return { tag: TAG_FP_REG, name: up, pos: r.pos, fmt: r.fmt, phys: r.phys };
    }
    return null;
}

function _tryString(token, _line) {
    if (token.startsWith('"') && token.endsWith('"')) {
        return { tag: TAG_STRING, text: token.slice(1, -1) };
    }
    return null;
}

function _tryConst(token, line) {
    if (_RE_CHAR_MULTI.test(token)) {
        throw new AsmError("Only one character is allowed", line);
    }
    const val = _tryParseNumber(token);
    if (val !== null) {
        _checkByteRange(val, line);
        return { tag: TAG_CONST, value: val };
    }
    return null;
}

// ── Shared float parsing ─────────────────────────────────────────

function _resolveFloatSuffix(suffixStr, line, defaultFmt, rejectNarrow) {
    if (suffixStr == null) return defaultFmt;
    const suffix = suffixStr.slice(1).toUpperCase();
    if (!(suffix in FP_DB_SUFFIX_TO_FMT)) {
        throw new AsmError("Invalid float literal", line);
    }
    const fmt = FP_DB_SUFFIX_TO_FMT[suffix];
    if (rejectNarrow && (fmt === FP_FMT_N1 || fmt === FP_FMT_N2)) {
        throw new AsmError(`Unsupported float format for DB: ${suffixStr.slice(1)}`, line);
    }
    return fmt;
}

function _parseFloatValue(token, line, tag, defaultFmt, rejectNarrow) {
    let m = _RE_FLOAT_SPECIAL.exec(token);
    if (m) {
        const fmt = _resolveFloatSuffix(m[3] || null, line, defaultFmt, rejectNarrow);
        let val;
        if (m[2].toLowerCase() === "inf") {
            val = m[1] === "-" ? -Infinity : Infinity;
        } else {
            val = NaN;
            if (m[1] === "-") val = -val;
        }
        return { tag, value: val, fmt };
    }

    m = _RE_FLOAT.exec(token);
    if (m) {
        const fmt = _resolveFloatSuffix(m[4] || null, line, defaultFmt, rejectNarrow);
        const text = (m[1] || "") + m[2] + (m[3] || "");
        const val = parseFloat(text);
        if (Number.isNaN(val) && text.toLowerCase() !== "nan") {
            throw new AsmError("Invalid float literal", line);
        }
        return { tag, value: val, fmt };
    }

    return null;
}

function _tryFpImm(token, line) {
    return _parseFloatValue(token, line, TAG_FP_IMM, null, false);
}

function _tryLabel(token, _line) {
    if (_RE_LABEL.test(token)) {
        return { tag: TAG_LABEL, name: token.toLowerCase() };
    }
    return null;
}

const _OPERAND_PARSERS = [_tryBracket, _tryRegister, _tryString, _tryConst, _tryFpImm, _tryLabel];

function _parseOperand(token, line) {
    token = token.trim();
    for (const parser of _OPERAND_PARSERS) {
        const result = parser(token, line);
        if (result !== null) return result;
    }
    throw new AsmError(`Invalid operand: ${token}`, line);
}

// ── Float literal for DB ─────────────────────────────────────────

function _parseFloatLiteral(token, line) {
    return _parseFloatValue(token, line, TAG_FLOAT, FP_FMT_F, true);
}

// ── DB operand parsing ───────────────────────────────────────────

function _parseDbOperands(raw, line, arch) {
    raw = raw.trim();

    // String literal
    if (raw.startsWith('"') && raw.endsWith('"')) {
        return [{ tag: TAG_STRING, text: raw.slice(1, -1) }];
    }

    const parts = raw.split(",").map((p) => p.trim());
    const operands = [];
    let hasFloat = false;
    let hasInt = false;

    for (const part of parts) {
        if (!part) continue;
        if (part.startsWith("[")) {
            throw new AsmError("DB does not support this operand", line);
        }
        const up = part.toUpperCase();
        if (up in REGISTERS) {
            throw new AsmError("DB does not support this operand", line);
        }

        // Try float literal first (if arch >= 2)
        if (arch >= 2) {
            const fp = _parseFloatLiteral(part, line);
            if (fp !== null) {
                if (hasInt) {
                    throw new AsmError("DB does not support mixing float and integer operands", line);
                }
                hasFloat = true;
                operands.push(fp);
                continue;
            }
        }

        // Integer value
        if (hasFloat) {
            throw new AsmError("DB does not support mixing float and integer operands", line);
        }

        if (_RE_LABEL.test(part) && _tryParseNumber(part) === null) {
            throw new AsmError("DB does not support this operand", line);
        }

        hasInt = true;
        const val = _parseNumber(part, line);
        _checkByteRange(val, line);
        operands.push({ tag: TAG_CONST, value: val });
    }
    return operands;
}

// ── Line tokenization ────────────────────────────────────────────

function _tokenizeLine(line) {
    const result = [];
    let inString = false;
    let i = 0;
    while (i < line.length) {
        const ch = line[i];
        if (ch === '"') {
            inString = !inString;
        } else if (ch === "'" && !inString) {
            if (i + 2 < line.length && line[i + 2] === "'") {
                result.push(line[i], line[i + 1], line[i + 2]);
                i += 3;
                continue;
            }
        } else if (ch === ";" && !inString) {
            break;
        }
        result.push(ch);
        i += 1;
    }
    return result.join("").trim();
}

function _splitOperands(operandStr) {
    const parts = [];
    const current = [];
    let depth = 0;
    let inString = false;

    for (const ch of operandStr) {
        if (ch === '"') {
            inString = !inString;
        } else if (ch === "[" && !inString) {
            depth += 1;
        } else if (ch === "]" && !inString) {
            depth -= 1;
        } else if (ch === "," && depth === 0 && !inString) {
            parts.push(current.join("").trim());
            current.length = 0;
            continue;
        }
        current.push(ch);
    }

    if (current.length > 0) {
        parts.push(current.join("").trim());
    }
    return parts.filter((p) => p.length > 0);
}

// ── Line parsing ─────────────────────────────────────────────────

const _RE_LABEL_DEF = /^([.A-Za-z]\w*)\s*:/;

function _parseLine(raw, lineNo, arch) {
    const text = _tokenizeLine(raw);

    const result = {
        lineNo,
        label: null,
        mnemonic: null,
        operands: null,
        dstSuffix: null,
        srcSuffix: null,
    };

    if (!text) return result;

    let remaining = text;

    // Check for label
    const labelMatch = _RE_LABEL_DEF.exec(remaining);
    if (labelMatch) {
        const labelName = labelMatch[1];
        const up = labelName.toUpperCase();
        if (up in REGISTERS || (arch >= 2 && FORBIDDEN_FP_LABEL_NAMES.has(up))) {
            throw new AsmError(`Label contains keyword: ${up}`, lineNo);
        }
        result.label = labelName.toLowerCase();
        remaining = remaining.slice(labelMatch[0].length).trim();
    }

    if (!remaining) return result;

    // Split mnemonic from operands
    const spaceIdx = remaining.search(/\s/);
    let mnemonicRaw, operandStr;
    if (spaceIdx === -1) {
        mnemonicRaw = remaining.toUpperCase();
        operandStr = "";
    } else {
        mnemonicRaw = remaining.slice(0, spaceIdx).toUpperCase();
        operandStr = remaining.slice(spaceIdx + 1).trim();
    }

    // Resolve aliases
    let mnemonic = MNEMONIC_ALIASES[mnemonicRaw] || mnemonicRaw;

    // Check for FP mnemonic with dot-suffix
    let dstSuffix = null;
    let srcSuffix = null;
    if (mnemonic.includes(".") && arch >= 2) {
        const dotParts = mnemonic.split(".");
        const base = dotParts[0];
        if (MNEMONICS_FP.has(base)) {
            mnemonic = base;
            dstSuffix = dotParts.length > 1 ? dotParts[1] : null;
            srcSuffix = dotParts.length > 2 ? dotParts[2] : null;
            if (dotParts.length > 3) {
                throw new AsmError("Syntax error", lineNo);
            }
        }
    }

    const allMnemonics = arch < 2 ? MNEMONICS : ALL_MNEMONICS_V2;

    if (!allMnemonics.has(mnemonic)) {
        if (_RE_LABEL.test(mnemonicRaw)) {
            throw new AsmError(`Invalid instruction: ${mnemonicRaw}`, lineNo);
        }
        throw new AsmError("Syntax error", lineNo);
    }

    // Validate FP suffix requirements
    if (arch >= 2 && MNEMONICS_FP.has(mnemonic)) {
        if (FP_CONTROL_MNEMONICS.has(mnemonic)) {
            if (dstSuffix !== null) {
                throw new AsmError("Syntax error", lineNo);
            }
        } else if (mnemonic === "FCVT") {
            if (dstSuffix === null || srcSuffix === null) {
                throw new AsmError("FP format suffix required", lineNo);
            }
        } else {
            if (dstSuffix === null) {
                throw new AsmError("FP format suffix required", lineNo);
            }
        }
    }

    result.mnemonic = mnemonic;
    result.dstSuffix = dstSuffix;
    result.srcSuffix = srcSuffix;

    // Parse operands based on mnemonic
    if (mnemonic === "DB") {
        result.operands = _parseDbOperands(operandStr, lineNo, arch);
        return result;
    }

    if (mnemonic === "HLT" || mnemonic === "RET" || mnemonic === "FCLR") {
        if (operandStr) {
            throw new AsmError(`${mnemonic}: too many arguments`, lineNo);
        }
        result.operands = [];
        return result;
    }

    result.operands = operandStr ? _splitOperands(operandStr).map((t) => _parseOperand(t, lineNo)) : [];
    return result;
}

function _parseLines(source, arch) {
    const lines = source.split("\n");
    const parsed = [];
    const labelsSeen = {};

    for (let i = 0; i < lines.length; i++) {
        const lineNo = i + 1;
        const p = _parseLine(lines[i], lineNo, arch);

        if (p.label !== null) {
            if (p.label in labelsSeen) {
                throw new AsmError(`Duplicate label: ${p.label}`, lineNo);
            }
            labelsSeen[p.label] = lineNo;
        }

        parsed.push(p);
    }

    return parsed;
}

// ── Operand matching ─────────────────────────────────────────────

function _operandMatches(op, ot) {
    switch (ot) {
        case OpType.REG:
            return op.tag === TAG_REG;
        case OpType.REG_STACK:
            return op.tag === TAG_REG && STACK_CODES.has(op.code);
        case OpType.REG_GPR:
            return op.tag === TAG_REG && GPR_CODES.has(op.code);
        case OpType.IMM:
            return op.tag === TAG_CONST || op.tag === TAG_LABEL;
        case OpType.MEM:
            return op.tag === TAG_ADDR || op.tag === TAG_ADDR_LABEL;
        case OpType.REGADDR:
            return op.tag === TAG_REGADDR;
        case OpType.FP_REG:
            return op.tag === TAG_FP_REG;
        case OpType.FP_IMM8:
        case OpType.FP_IMM16:
            return op.tag === TAG_FP_IMM;
        default:
            return false;
    }
}

// ── Operand encoding ─────────────────────────────────────────────

function _encodeOperand(op) {
    switch (op.tag) {
        case TAG_REG:
            return op.code;
        case TAG_CONST:
            return op.value;
        case TAG_ADDR:
            return op.value;
        case TAG_REGADDR:
            return encodeRegaddr(op.regCode, op.offset);
        case TAG_LABEL:
            return 0; // placeholder for pass 2
        case TAG_ADDR_LABEL:
            return 0; // placeholder for pass 2
        default:
            throw new Error(`unexpected operand: ${op.tag}`);
    }
}

// ── Instruction matching ─────────────────────────────────────────

function _findInsn(mnemonic, operands, line, table) {
    if (table == null) table = BY_MNEMONIC;
    const candidates = table[mnemonic];
    if (!candidates) {
        throw new AsmError(`Invalid instruction: ${mnemonic}`, line);
    }

    for (const instr of candidates) {
        if (instr.sig.length !== operands.length) continue;
        if (instr.sig.every((ot, i) => _operandMatches(operands[i], ot))) return instr;
    }

    const maxArity = Math.max(...candidates.map((i) => i.sig.length));
    if (operands.length > maxArity) {
        throw new AsmError(`${mnemonic}: too many arguments`, line);
    }
    throw new AsmError(`${mnemonic} does not support this operand(s)`, line);
}

// ── FP float encoding helper ─────────────────────────────────────

function _encodeFloat(value, fmt, line) {
    const { data, exc } = floatToBytes(value, fmt);
    if (exc.overflow && fmt === FP_FMT_O3) {
        throw new AsmError("Float value out of range for format E4M3", line);
    }
    return data;
}

// ── DB encoding ──────────────────────────────────────────────────

function _encodeDbOperand(op, line, result) {
    if (op.tag === TAG_CONST) {
        result.push(op.value);
        return;
    }
    if (op.tag === TAG_STRING) {
        if (!op.text) {
            throw new AsmError("DB string must not be empty", line);
        }
        for (const c of op.text) result.push(c.charCodeAt(0));
        return;
    }
    if (op.tag === TAG_FLOAT) {
        result.push(..._encodeFloat(op.value, op.fmt, line));
        return;
    }
    throw new AsmError("DB does not support this operand", line);
}

function _encodeDb(operands, line) {
    const result = [];
    for (const op of operands) {
        _encodeDbOperand(op, line, result);
    }
    return result;
}

// ── FP suffix validation ─────────────────────────────────────────

function _validateFpSuffix(suffix, line) {
    const upper = suffix.toUpperCase();
    if (!(upper in FP_SUFFIX_TO_FMT)) {
        throw new AsmError(`Invalid FP format suffix: .${suffix}`, line);
    }
    return FP_SUFFIX_TO_FMT[upper];
}

function _validateFpRegWidth(reg, fmt, line) {
    const fmtWidth = FP_FMT_WIDTH[fmt];
    const allowed = FP_WIDTH_REGS[fmtWidth];
    if (!allowed || !allowed.has(reg.name)) {
        throw new AsmError("FP format suffix does not match register width", line);
    }
}

// ── FP instruction encoding ──────────────────────────────────────

function _encodeFpInstruction(instr, operands, dstSuffix, srcSuffix, line) {
    const dstFmt = dstSuffix ? _validateFpSuffix(dstSuffix, line) : null;
    const srcFmt = srcSuffix ? _validateFpSuffix(srcSuffix, line) : null;

    // FCVT special case: dual suffix
    if (instr.op === Op.FCVT_FP_FP) {
        if (dstFmt === srcFmt) {
            throw new AsmError("FCVT with identical formats (use FMOV)", line);
        }
        const dstReg = operands[0];
        const srcReg = operands[1];
        _validateFpRegWidth(dstReg, dstFmt, line);
        _validateFpRegWidth(srcReg, srcFmt, line);
        const dstFpm = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);
        const srcFpm = encodeFpm(srcReg.phys, srcReg.pos, srcFmt);
        return [instr.op, dstFpm, srcFpm];
    }

    const fpOps = [];
    const nonFpOps = [];
    for (const op of operands) {
        if (op.tag === TAG_FP_REG) {
            _validateFpRegWidth(op, dstFmt, line);
            fpOps.push(op);
        } else {
            nonFpOps.push(op);
        }
    }

    const fpmBytes = fpOps.map((fp) => encodeFpm(fp.phys, fp.pos, dstFmt));
    const nonFpBytes = nonFpOps.map((op) => _encodeOperand(op));

    return [instr.op, ...fpmBytes, ...nonFpBytes];
}

// ── FMOV immediate encoding ─────────────────────────────────────

function _encodeFmovImm(operands, dstSuffix, line) {
    if (operands[0].tag !== TAG_FP_REG) {
        throw new AsmError("FMOV does not support this operand(s)", line);
    }

    const dstReg = operands[0];
    const fpImm = operands[1];
    const dstFmt = _validateFpSuffix(dstSuffix, line);
    const fmtWidth = FP_FMT_WIDTH[dstFmt];

    if (fmtWidth === 32) {
        throw new AsmError("FP immediate not supported for float32", line);
    }
    if (fmtWidth === 4) {
        throw new AsmError("FP immediate not supported for 4-bit formats", line);
    }

    // Check literal suffix matches instruction suffix
    if (fpImm.fmt !== null && fpImm.fmt !== dstFmt) {
        throw new AsmError("FP immediate suffix mismatch", line);
    }

    _validateFpRegWidth(dstReg, dstFmt, line);

    const data = _encodeFloat(fpImm.value, dstFmt, line);
    const fpmByte = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);

    if (fmtWidth === 8) {
        return [Op.FMOV_FP_IMM8, fpmByte, data[0]];
    }
    return [Op.FMOV_FP_IMM16, fpmByte, data[0], data[1]];
}

// ── Instruction encoding ─────────────────────────────────────────

function _encodeInstruction(mnemonic, operands, line, dstSuffix, srcSuffix, arch) {
    if (mnemonic === "DB") {
        return _encodeDb(operands, line);
    }

    if (arch >= 2 && MNEMONICS_FP.has(mnemonic)) {
        // FMOV immediate special case
        if (mnemonic === "FMOV" && operands.length === 2 && operands[1].tag === TAG_FP_IMM) {
            return _encodeFmovImm(operands, dstSuffix, line);
        }

        const instr = _findInsn(mnemonic, operands, line, BY_MNEMONIC_FP);
        if (FP_CONTROL_MNEMONICS.has(mnemonic)) {
            return [instr.op, ...operands.map((op) => _encodeOperand(op))];
        }
        return _encodeFpInstruction(instr, operands, dstSuffix, srcSuffix, line);
    }

    const instr = _findInsn(mnemonic, operands, line, BY_MNEMONIC);
    return [instr.op, ...operands.map((op) => _encodeOperand(op))];
}

// ── Phase 0: @include preprocessing ──────────────────────────────

const _MAX_INCLUDE_DEPTH = 16;

/**
 * Collect lines from source into outLines, building lineMap (1-based flat line → {file, line}).
 * Mutates outLines and lineMap in place (mirrors Python's _collect pattern).
 */
function _collectLines(source, files, filename, visited, depth, outLines, lineMap) {
    const lines = source.split("\n");
    for (let i = 0; i < lines.length; i++) {
        const lineNo = i + 1;
        const text = lines[i];
        if (_RE_INCLUDE_START.test(text)) {
            const m = _RE_INCLUDE_FULL.exec(text);
            if (!m || !m[1]) {
                throw new AsmError("@include: invalid syntax", lineNo, filename);
            }
            const path = m[1];
            if (!(path in files)) {
                const msg = _isUrl(path)
                    ? `@include: URL not pre-fetched (use assembleAsync): ${path}`
                    : `@include: file not found: ${path}`;
                throw new AsmError(msg, lineNo, filename);
            }
            if (visited.has(path)) {
                throw new AsmError(`@include: circular include: ${path}`, lineNo, filename);
            }
            if (depth >= _MAX_INCLUDE_DEPTH) {
                throw new AsmError("@include: max include depth exceeded", lineNo, filename);
            }
            const included = files[path];
            if (included instanceof Uint8Array || included instanceof ArrayBuffer) {
                // Binary file: embed raw bytes as a single DB directive.
                const bytes = included instanceof ArrayBuffer ? new Uint8Array(included) : included;
                if (bytes.length > 0) {
                    const flatLineNo = outLines.length + 1;
                    lineMap.set(flatLineNo, { file: filename, line: lineNo });
                    outLines.push("DB " + Array.from(bytes).join(", "));
                }
            } else {
                _collectLines(included, files, path, new Set([...visited, path]), depth + 1, outLines, lineMap);
            }
        } else {
            const flatLineNo = outLines.length + 1;
            lineMap.set(flatLineNo, { file: filename, line: lineNo });
            outLines.push(text);
        }
    }
}

function _preprocess(source, files) {
    const outLines = [];
    const lineMap = new Map(); // flatLine (1-based) → { file: string|null, line: number }
    _collectLines(source, files, null, new Set(), 0, outLines, lineMap);
    return { flat: outLines.join("\n"), lineMap };
}

// ── Two-pass assembly (pass 1 + pass 2) ──────────────────────────

export function assemble(source, arch = 2, files = {}) {
    // Phase 0: preprocessing (errors thrown here already carry correct filename)
    const { flat, lineMap } = _preprocess(source, files);

    // Translate a flat-source AsmError to original file + line using lineMap
    const _locErr = (e) => {
        if (e instanceof AsmError) {
            const loc = lineMap.get(e.line);
            if (loc) return new AsmError(e.message, loc.line, loc.file);
        }
        return e;
    };

    let parsed;
    try {
        parsed = _parseLines(flat, arch);
    } catch (e) {
        throw _locErr(e);
    }

    // Pass 1: generate code, collect labels
    const code = [];
    const labels = {};
    const mapping = {};
    const labelPatches = []; // [patchPos, labelName, lineNo]

    try {
        for (const pline of parsed) {
            const pos = code.length;

            if (pline.label !== null) {
                labels[pline.label] = pos;
            }

            if (pline.mnemonic === null) continue;

            const operands = pline.operands || [];

            const encoded = _encodeInstruction(
                pline.mnemonic,
                operands,
                pline.lineNo,
                pline.dstSuffix,
                pline.srcSuffix,
                arch,
            );

            if (pline.mnemonic !== "DB") {
                mapping[pos] = pline.lineNo;
            }

            for (let i = 0; i < operands.length; i++) {
                const op = operands[i];
                if (op.tag !== TAG_LABEL && op.tag !== TAG_ADDR_LABEL) continue;
                const isFpData =
                    arch >= 2 && MNEMONICS_FP.has(pline.mnemonic) && !FP_CONTROL_MNEMONICS.has(pline.mnemonic);
                if (isFpData) {
                    const fpCount = operands.filter((o) => o.tag === TAG_FP_REG).length;
                    const nonFpIdx = operands.slice(0, i).filter((o) => o.tag !== TAG_FP_REG).length;
                    labelPatches.push([pos + 1 + fpCount + nonFpIdx, op.name, pline.lineNo]);
                } else {
                    labelPatches.push([pos + 1 + i, op.name, pline.lineNo]);
                }
            }

            code.push(...encoded);
        }

        // Pass 2: resolve labels
        for (const [patchPos, labelName, lineNo] of labelPatches) {
            if (!(labelName in labels)) {
                throw new AsmError(`Undefined label: ${labelName}`, lineNo);
            }
            const addr = labels[labelName];
            if (addr < 0 || addr > 255) {
                throw new AsmError(`${addr} must have a value between 0-255`, lineNo);
            }
            code[patchPos] = addr;
        }
    } catch (e) {
        throw _locErr(e);
    }

    return { code, labels, mapping, lineMap };
}

// ── Async assembly with URL @include support ──────────────────────

async function _prefetchUrls(source, allFiles, visited, depth) {
    if (depth >= _MAX_INCLUDE_DEPTH) return;

    // Phase 1: scan — collect new URL includes with their line numbers
    const lines = source.split("\n");
    const urlLines = new Map(); // url → lineNo
    for (let i = 0; i < lines.length; i++) {
        const m = _RE_INCLUDE_FULL.exec(lines[i]);
        if (!m || !_isUrl(m[1]) || visited.has(m[1])) continue;
        visited.add(m[1]);
        urlLines.set(m[1], i + 1);
    }

    // Phase 2: fetch missing URLs in parallel
    await Promise.all(
        [...urlLines.entries()]
            .filter(([url]) => !(url in allFiles))
            .map(async ([url, lineNo]) => {
                try {
                    const resp = await fetch(url);
                    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
                    const bytes = new Uint8Array(await resp.arrayBuffer());
                    allFiles[url] = _decodeUtf8(bytes) ?? bytes;
                } catch (e) {
                    throw new AsmError(`@include: fetch failed: ${url}: ${e.message}`, lineNo, null);
                }
            }),
    );

    // Phase 3: recurse into text files in parallel
    await Promise.all(
        [...urlLines.keys()]
            .filter((url) => typeof allFiles[url] === "string")
            .map((url) => _prefetchUrls(allFiles[url], allFiles, visited, depth + 1)),
    );
}

/**
 * Assemble with URL @include support. Fetches all URL includes before assembling.
 * Use this instead of assemble() when the source may contain @include "https://..." directives.
 */
export async function assembleAsync(source, arch = 2, files = {}) {
    const allFiles = { ...files };
    await _prefetchUrls(source, allFiles, new Set(), 0);
    return assemble(source, arch, allFiles);
}
