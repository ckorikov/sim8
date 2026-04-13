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
    FORBIDDEN_FP_LABEL_NAMES,
    VU_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_MODE,
    VU_CMP_SUFFIX,
    // Re-exported for asm.js codegen (avoids redundant asm.js → isa.js edge)
    Op,
    OpType,
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    GPR_CODES,
    ARITH_CODES,
    STACK_CODES,
    FP_SUFFIX_TO_FMT,
    FP_FMT_WIDTH,
    FP_WIDTH_REGS,
    FP_FMT_O3,
    encodeRegaddr,
    encodeFpm,
} from "./isa.js";

import {
    AsmError,
    TAG_CONST,
    TAG_REG,
    TAG_ADDR,
    TAG_REGADDR,
    TAG_STRING,
    TAG_LABEL,
    TAG_ADDR_LABEL,
    TAG_FP_REG,
    TAG_FLOAT,
    TAG_FP_IMM,
    TAG_VU_REG,
    TAG_PAGE_LABEL,
    _VU_REG_MAP,
    _RE_LABEL,
    _tryParseNumber,
    _parseOperand,
    _parseDbOperands,
    _tokenizeLine,
    _splitOperands,
} from "./_asm-parse-ops.js";

export {
    AsmError,
    TAG_REG,
    TAG_CONST,
    TAG_ADDR,
    TAG_REGADDR,
    TAG_STRING,
    TAG_LABEL,
    TAG_ADDR_LABEL,
    TAG_FP_REG,
    TAG_FLOAT,
    TAG_FP_IMM,
    TAG_VU_REG,
    TAG_PAGE_LABEL,
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

// ── Cached combined mnemonic sets ────────────────────────────────

const ALL_MNEMONICS_V2 = new Set([...MNEMONICS, ...MNEMONICS_FP]);
const ALL_MNEMONICS_V3 = new Set([...ALL_MNEMONICS_V2, ...MNEMONICS_VU]);

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

// ── Zero-operand mnemonics ───────────────────────────────────────

const _ZERO_ARG_MNEMONICS = new Set(["HLT", "RET", "FCLR", "VFCLR", "VWAIT"]);

function _validateFpSuffixReqs(mnemonic, dstSuffix, srcSuffix, lineNo) {
    if (FP_CONTROL_MNEMONICS.has(mnemonic)) {
        if (dstSuffix !== null) throw new AsmError("Syntax error", lineNo);
    } else if (mnemonic === "FCVT") {
        if (dstSuffix === null || srcSuffix === null) throw new AsmError("FP format suffix required", lineNo);
    } else {
        if (dstSuffix === null) throw new AsmError("FP format suffix required", lineNo);
    }
}

function _validateVuSuffixReqs(mnemonic, vuFmtSuffix, vuModeSuffix, vuCondSuffix, lineNo) {
    if (VU_SYNC_MNEMONICS.has(mnemonic)) {
        if (vuFmtSuffix !== null) throw new AsmError("Syntax error", lineNo);
    } else {
        if (vuFmtSuffix === null) throw new AsmError("VU format suffix required", lineNo);
        if (!(vuFmtSuffix in VU_SUFFIX_TO_FMT)) throw new AsmError(`Invalid VU format suffix: ${vuFmtSuffix}`, lineNo);
        if (vuModeSuffix !== null && !(vuModeSuffix in VU_SUFFIX_TO_MODE))
            throw new AsmError(`Invalid VU mode suffix: ${vuModeSuffix}`, lineNo);
        if (vuCondSuffix !== null && !(vuCondSuffix in VU_CMP_SUFFIX))
            throw new AsmError(`Invalid VU condition suffix: ${vuCondSuffix}`, lineNo);
    }
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

    if (_RE_PAGE_DIRECTIVE.test(text)) return _parsePageDirective(text, lineNo, result);

    let remaining = text;

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

    const spaceIdx = remaining.search(/\s/);
    let mnemonicRaw, operandStr;
    if (spaceIdx === -1) {
        mnemonicRaw = remaining.toUpperCase();
        operandStr = "";
    } else {
        mnemonicRaw = remaining.slice(0, spaceIdx).toUpperCase();
        operandStr = remaining.slice(spaceIdx + 1).trim();
    }

    let mnemonic = MNEMONIC_ALIASES[mnemonicRaw] || mnemonicRaw;

    let dstSuffix = null;
    let srcSuffix = null;
    let vuFmtSuffix = null;
    let vuModeSuffix = null;
    let vuCondSuffix = null;
    if (mnemonic.includes(".") && arch >= 2) {
        const dotParts = mnemonic.split(".");
        const base = dotParts[0];
        if (arch >= 3 && MNEMONICS_VU.has(base)) {
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

    if (arch >= 2 && MNEMONICS_FP.has(mnemonic)) _validateFpSuffixReqs(mnemonic, dstSuffix, srcSuffix, lineNo);
    if (arch >= 3 && MNEMONICS_VU.has(mnemonic))
        _validateVuSuffixReqs(mnemonic, vuFmtSuffix, vuModeSuffix, vuCondSuffix, lineNo);

    result.mnemonic = mnemonic;
    result.dstSuffix = dstSuffix;
    result.srcSuffix = srcSuffix;
    result.vuFmtSuffix = vuFmtSuffix;
    result.vuModeSuffix = vuModeSuffix;
    result.vuCondSuffix = vuCondSuffix;

    if (mnemonic === "DB") {
        result.operands = _parseDbOperands(operandStr, lineNo, arch);
        return result;
    }

    if (_ZERO_ARG_MNEMONICS.has(mnemonic)) {
        if (operandStr) throw new AsmError(`${mnemonic}: too many arguments`, lineNo);
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
