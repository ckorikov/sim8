/**
 * Low-level operand parsing: tags, number parsers, bracket parsers,
 * operand dispatchers, float/DB parsers, tokenizer.
 * Internal module — consumed only by asm-parse.js.
 */

import { Reg, FP_REGISTERS, FP_SUFFIX_TO_FMT, FP_FMT_F, FP_FMT_N1, FP_FMT_N2 } from "./isa.js";

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

// ── VU register map (also needed by line parser for keyword check) ─

export const _VU_REG_MAP = { VA: 0, VB: 1, VC: 2, VM: 3, VL: 4 };

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

export function _tryParseNumber(token) {
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

// ── Label regex ──────────────────────────────────────────────────

export const _RE_LABEL = /^[.A-Za-z]\w*$/;

// ── Float literal parsing ────────────────────────────────────────

const _RE_FLOAT = /^([+-]?)(\d+\.\d*|\.\d+)([eE][+-]?\d+)?(_\w+)?$/;
const _RE_FLOAT_SPECIAL = /^([+-]?)(inf|nan)(_\w+)?$/i;

// ── Bracket operand parsing ──────────────────────────────────────

const _RE_BRACKET = /^\[(.+)\]$/;
const _RE_REG_OFFSET = /^([A-Za-z]+)\s*([+-])\s*(\d+)$/;
const _RE_REG_ONLY = /^([A-Za-z]+)$/;
const _RE_LABEL_OFFSET = /^([.A-Za-z]\w*)\s*([+-])\s*(\d+)$/;

function _parseBracketOperand(inner, line) {
    inner = inner.trim();

    let m = _RE_REG_OFFSET.exec(inner);
    if (m) {
        const regName = m[1].toUpperCase();
        const sign = m[2];
        let offsetVal = parseInt(m[3], 10);
        if (sign === "-") offsetVal = -offsetVal;
        if (regName in Reg) {
            if (offsetVal < -16 || offsetVal > 15) {
                throw new AsmError("offset must be a value between -16...+15", line);
            }
            return { tag: TAG_REGADDR, regCode: Reg[regName], offset: offsetVal };
        }
    }

    m = _RE_LABEL_OFFSET.exec(inner);
    if (m) {
        const name = m[1];
        const sign = m[2];
        let offsetVal = parseInt(m[3], 10);
        if (sign === "-") offsetVal = -offsetVal;
        return { tag: TAG_ADDR_LABEL, name: name.toLowerCase(), offset: offsetVal };
    }

    m = _RE_REG_ONLY.exec(inner);
    if (m) {
        const regName = m[1].toUpperCase();
        if (regName in Reg) {
            return { tag: TAG_REGADDR, regCode: Reg[regName], offset: 0 };
        }
    }

    const val = _tryParseNumber(inner);
    if (val !== null) {
        _checkByteRange(val, line);
        return { tag: TAG_ADDR, value: val };
    }

    if (_RE_LABEL.test(inner)) {
        return { tag: TAG_ADDR_LABEL, name: inner.toLowerCase(), offset: 0 };
    }

    throw new AsmError(`Invalid address: ${inner}`, line);
}

// ── Operand parsers ──────────────────────────────────────────────

function _tryBracket(token, line) {
    const m = _RE_BRACKET.exec(token);
    if (m) return _parseBracketOperand(m[1], line);
    return null;
}

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

export function _parseOperand(token, line, arch = 1, wide = false) {
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

export function _parseDbOperands(raw, line, arch) {
    raw = raw.trim();

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

export function _tokenizeLine(line) {
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

export function _splitOperands(operandStr) {
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
