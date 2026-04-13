/**
 * FP instruction encoding for the sim8 assembler.
 */

import { floatToBytes } from "./fp.js";

import {
    Op,
    AsmError,
    FP_SUFFIX_TO_FMT,
    FP_FMT_WIDTH,
    FP_WIDTH_REGS,
    FP_FMT_O3,
    encodeFpm,
    TAG_FP_REG,
    TAG_CONST,
    TAG_STRING,
    TAG_FLOAT,
} from "./asm-parse.js";

import { _encodeOperand, _lookupSuffix } from "./asm-core.js";

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

export function _encodeDb(operands, line) {
    const result = [];
    for (const op of operands) {
        _encodeDbOperand(op, line, result);
    }
    return result;
}

// ── FP suffix validation ─────────────────────────────────────────

function _validateFpSuffix(suffix, line) {
    return _lookupSuffix(suffix, FP_SUFFIX_TO_FMT, "Invalid FP format suffix", line);
}

function _validateFpRegWidth(reg, fmt, line) {
    const fmtWidth = FP_FMT_WIDTH[fmt];
    const allowed = FP_WIDTH_REGS[fmtWidth];
    if (!allowed || !allowed.has(reg.name)) {
        throw new AsmError("FP format suffix does not match register width", line);
    }
}

// ── FP instruction encoding ──────────────────────────────────────

export function _encodeFpInstruction(instr, operands, dstSuffix, srcSuffix, line) {
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
        const dstFpmEnc = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);
        const srcFpmEnc = encodeFpm(srcReg.phys, srcReg.pos, srcFmt);
        return [instr.op, dstFpmEnc, srcFpmEnc];
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

    const fpmEncs = fpOps.map((fp) => encodeFpm(fp.phys, fp.pos, dstFmt));
    const nonFpBytes = nonFpOps.map((op) => _encodeOperand(op));

    return [instr.op, ...fpmEncs, ...nonFpBytes];
}

// ── FMOV immediate encoding ─────────────────────────────────────

export function _encodeFmovImm(operands, dstSuffix, line) {
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
    const fpmEnc = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);

    if (fmtWidth === 8) {
        return [Op.FMOV_FP_IMM8, fpmEnc, data[0]];
    }
    return [Op.FMOV_FP_IMM16, fpmEnc, data[0], data[1]];
}
