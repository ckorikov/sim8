/**
 * Assembly source parser: tokenizer, operand parsing, line parsing.
 * Extracted from asm.js — pure parsing with zero codegen dependency.
 */

import {
    // Used by parser
    Reg,
    MNEMONICS,
    MNEMONICS_FP,
    MNEMONICS_VU,
    FP_CONTROL_MNEMONICS,
    VU_SYNC_MNEMONICS,
    MNEMONIC_ALIASES,
    FP_REGISTERS,
    FORBIDDEN_FP_LABEL_NAMES,
    FP_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_MODE,
    VU_CMP_SUFFIX,
    FP_FMT_F,
    FP_FMT_N1,
    FP_FMT_N2,
    // Re-exported for asm.js codegen (avoids redundant asm.js → isa.js edge)
    Op,
    OpType,
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    GPR_CODES,
    ARITH_CODES,
    STACK_CODES,
    FP_FMT_WIDTH,
    FP_WIDTH_REGS,
    FP_FMT_O3,
    encodeRegaddr,
    encodeFpm,
} from "./isa.js";

export {
    Op,
    OpType,
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    MNEMONICS_FP,
    MNEMONICS_VU,
    FP_CONTROL_MNEMONICS,
    GPR_CODES,
    ARITH_CODES,
    STACK_CODES,
    FP_SUFFIX_TO_FMT,
    FP_FMT_WIDTH,
    FP_WIDTH_REGS,
    FP_FMT_O3,
    encodeRegaddr,
    encodeFpm,
};

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

// ── Cached combined mnemonic sets ────────────────────────────────

const ALL_MNEMONICS_V2 = new Set([...MNEMONICS, ...MNEMONICS_FP]);
const ALL_MNEMONICS_V3 = new Set([...ALL_MNEMONICS_V2, ...MNEMONICS_VU]);

// ── Operand tags ─────────────────────────────────────────────────

export const TAG_REG = "reg";
export const TAG_CONST = "const";
export const TAG_ADDR = "addr";
export const TAG_REGADDR = "regaddr";
export const TAG_STRING = "string";
export const TAG_LABEL = "label";
export const TAG_ADDR_LABEL = "addr_label";
export const TAG_FP_REG = "fp_reg";
export const TAG_FLOAT = "float";
export const TAG_FP_IMM = "fp_imm";
export const TAG_VU_REG = "vu_reg";
export const TAG_PAGE_LABEL = "page_label";

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

export const RE_INCLUDE_FULL = /^\s*@include\s+"([^"]+)"\s*$/i;
export const RE_INCLUDE_START = /^\s*@include\b/i;

export function isUrl(path) {
    return path.startsWith("http://") || path.startsWith("https://");
}

export function decodeUtf8(bytes) {
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
        if (!(regName in Reg)) {
            throw new AsmError(`Invalid register in address: ${m[1]}`, line);
        }
        if (offsetVal < -16 || offsetVal > 15) {
            throw new AsmError("offset must be a value between -16...+15", line);
        }
        return { tag: TAG_REGADDR, regCode: Reg[regName], offset: offsetVal };
    }

    // [reg]
    m = _RE_REG_ONLY.exec(inner);
    if (m) {
        const regName = m[1].toUpperCase();
        if (regName in Reg) {
            return { tag: TAG_REGADDR, regCode: Reg[regName], offset: 0 };
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

const _VU_REG_MAP = { VA: 0, VB: 1, VC: 2, VM: 3, VL: 4 };

function _tryRegister(token, _line, arch) {
    const up = token.toUpperCase();
    if (up in Reg) {
        return { tag: TAG_REG, code: Reg[up] };
    }
    if (up in FP_REGISTERS) {
        const r = FP_REGISTERS[up];
        return { tag: TAG_FP_REG, name: up, pos: r.pos, fmt: r.fmt, phys: r.phys };
    }
    if (arch >= 3 && up in _VU_REG_MAP) {
        return { tag: TAG_VU_REG, code: _VU_REG_MAP[up] };
    }
    return null;
}

function _tryString(token, _line) {
    if (token.startsWith('"') && token.endsWith('"')) {
        return { tag: TAG_STRING, text: token.slice(1, -1) };
    }
    return null;
}

function _tryConst(token, line, wide = false) {
    if (_RE_CHAR_MULTI.test(token)) {
        throw new AsmError("Only one character is allowed", line);
    }
    const val = _tryParseNumber(token);
    if (val !== null) {
        if (!wide) _checkByteRange(val, line);
        return { tag: TAG_CONST, value: val };
    }
    return null;
}

// ── Shared float parsing ─────────────────────────────────────────

function _resolveFloatSuffix(suffixStr, line, defaultFmt, rejectNarrow) {
    if (suffixStr == null) return defaultFmt;
    const suffix = suffixStr.slice(1).toUpperCase();
    if (!(suffix in FP_SUFFIX_TO_FMT)) {
        throw new AsmError("Invalid float literal", line);
    }
    const fmt = FP_SUFFIX_TO_FMT[suffix];
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

const _RE_PAGE_LABEL = /^\{(.+)\}$/;

function _tryPageLabel(token, line) {
    const m = _RE_PAGE_LABEL.exec(token);
    if (!m) return null;
    const inner = m[1].trim();
    if (!inner) throw new AsmError("Syntax error", line);
    if (!_RE_LABEL.test(inner)) throw new AsmError("Syntax error", line);
    return { tag: TAG_PAGE_LABEL, name: inner.toLowerCase() };
}

function _tryLabel(token, _line) {
    if (_RE_LABEL.test(token)) {
        return { tag: TAG_LABEL, name: token.toLowerCase() };
    }
    return null;
}

const _OPERAND_PARSERS = [_tryBracket, _tryPageLabel, _tryRegister, _tryString, _tryConst, _tryFpImm, _tryLabel];

function _parseOperand(token, line, arch = 1, wide = false) {
    token = token.trim();
    for (const parser of _OPERAND_PARSERS) {
        const result = parser === _tryConst ? parser(token, line, wide) : parser(token, line, arch);
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
        if (up in Reg) {
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
const _RE_PAGE_DIRECTIVE = /^\s*@page\b/i;
const _RE_PAGE_FULL = /^\s*@page\s+(\S+)(?:\s*,\s*(\S+))?\s*$/i;

function _parsePageDirective(text, lineNo, result) {
    if (/^[.A-Za-z]\w*\s*:/.test(text)) {
        throw new AsmError("@page must be on its own line", lineNo);
    }
    const m = _RE_PAGE_FULL.exec(text);
    if (!m) {
        if (/^\s*@page\s*$/i.test(text)) {
            throw new AsmError("@page: missing page number", lineNo);
        }
        throw new AsmError("@page: invalid syntax", lineNo);
    }
    const pageVal = _tryParseNumber(m[1]);
    if (pageVal === null) {
        throw new AsmError("@page: invalid syntax", lineNo);
    }
    if (pageVal < 0 || pageVal > 255) {
        throw new AsmError("@page value must be 0-255", lineNo);
    }
    result.mnemonic = "@PAGE";
    result.operands = [{ tag: TAG_CONST, value: pageVal }];
    if (m[2] !== undefined) {
        const offsetVal = _tryParseNumber(m[2]);
        if (offsetVal === null) {
            throw new AsmError("@page: invalid offset", lineNo);
        }
        if (offsetVal < 0 || offsetVal > 255) {
            throw new AsmError("@page offset must be 0-255", lineNo);
        }
        result.operands.push({ tag: TAG_CONST, value: offsetVal });
    }
    return result;
}

function _parseLine(raw, lineNo, arch) {
    const text = _tokenizeLine(raw);

    const result = {
        lineNo,
        label: null,
        mnemonic: null,
        operands: null,
        dstSuffix: null,
        srcSuffix: null,
        vuFmtSuffix: null,
        vuModeSuffix: null,
        vuCondSuffix: null,
    };

    if (!text) return result;

    // @page directive (must come before label check)
    if (_RE_PAGE_DIRECTIVE.test(text)) return _parsePageDirective(text, lineNo, result);

    let remaining = text;

    // Check for label
    const labelMatch = _RE_LABEL_DEF.exec(remaining);
    if (labelMatch) {
        const labelName = labelMatch[1];
        const up = labelName.toUpperCase();
        if (up in Reg || (arch >= 2 && FORBIDDEN_FP_LABEL_NAMES.has(up)) || (arch >= 3 && up in _VU_REG_MAP)) {
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

    // Check for FP or VU mnemonic with dot-suffix
    let dstSuffix = null;
    let srcSuffix = null;
    let vuFmtSuffix = null;
    let vuModeSuffix = null;
    let vuCondSuffix = null;
    if (mnemonic.includes(".") && arch >= 2) {
        const dotParts = mnemonic.split(".");
        const base = dotParts[0];
        if (arch >= 3 && MNEMONICS_VU.has(base)) {
            // VU: MNEMONIC.fmt[.mode][.cond] — up to 3 suffixes
            mnemonic = base;
            if (dotParts.length > 4) {
                throw new AsmError("Syntax error", lineNo);
            }
            vuFmtSuffix = dotParts.length > 1 ? dotParts[1] : null;
            vuModeSuffix = dotParts.length > 2 ? dotParts[2] : null;
            vuCondSuffix = dotParts.length > 3 ? dotParts[3] : null;
        } else if (MNEMONICS_FP.has(base)) {
            mnemonic = base;
            dstSuffix = dotParts.length > 1 ? dotParts[1] : null;
            srcSuffix = dotParts.length > 2 ? dotParts[2] : null;
            if (dotParts.length > 3) {
                throw new AsmError("Syntax error", lineNo);
            }
        }
    }

    const allMnemonics = arch < 2 ? MNEMONICS : arch < 3 ? ALL_MNEMONICS_V2 : ALL_MNEMONICS_V3;

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

    // Validate VU suffix requirements
    if (arch >= 3 && MNEMONICS_VU.has(mnemonic)) {
        if (VU_SYNC_MNEMONICS.has(mnemonic)) {
            if (vuFmtSuffix !== null) {
                throw new AsmError("Syntax error", lineNo);
            }
        } else {
            // Async VU instructions require format suffix
            if (vuFmtSuffix === null) {
                throw new AsmError("VU format suffix required", lineNo);
            }
            if (!(vuFmtSuffix in VU_SUFFIX_TO_FMT)) {
                throw new AsmError(`Invalid VU format suffix: ${vuFmtSuffix}`, lineNo);
            }
            if (vuModeSuffix !== null && !(vuModeSuffix in VU_SUFFIX_TO_MODE)) {
                throw new AsmError(`Invalid VU mode suffix: ${vuModeSuffix}`, lineNo);
            }
            if (vuCondSuffix !== null && !(vuCondSuffix in VU_CMP_SUFFIX)) {
                throw new AsmError(`Invalid VU condition suffix: ${vuCondSuffix}`, lineNo);
            }
        }
    }

    result.mnemonic = mnemonic;
    result.dstSuffix = dstSuffix;
    result.srcSuffix = srcSuffix;
    result.vuFmtSuffix = vuFmtSuffix;
    result.vuModeSuffix = vuModeSuffix;
    result.vuCondSuffix = vuCondSuffix;

    // Parse operands based on mnemonic
    if (mnemonic === "DB") {
        result.operands = _parseDbOperands(operandStr, lineNo, arch);
        return result;
    }

    if (
        mnemonic === "HLT" ||
        mnemonic === "RET" ||
        mnemonic === "FCLR" ||
        mnemonic === "VFCLR" ||
        mnemonic === "VWAIT"
    ) {
        if (operandStr) {
            throw new AsmError(`${mnemonic}: too many arguments`, lineNo);
        }
        result.operands = [];
        return result;
    }

    const wideImm = arch >= 3 && MNEMONICS_VU.has(mnemonic);
    result.operands = operandStr ? _splitOperands(operandStr).map((t) => _parseOperand(t, lineNo, arch, wideImm)) : [];
    return result;
}

export function parseLines(source, arch) {
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
