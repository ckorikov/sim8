/**
 * MU instruction encoding for the sim8 assembler.
 */

import { Op, MU_SYNC_MNEMONICS, MU_SUFFIX_TO_FMT, encodeMfm, encodeVuRegs } from "./isa.js";

import { AsmError, TAG_REG, TAG_CONST, TAG_MU_REG, TAG_LABEL, TAG_PAGE_LABEL, TAG_ADDR_LABEL } from "./asm-parse.js";

import { _lookupSuffix } from "./asm-core.js";

// ── MU instruction encoding ──────────────────────────────────────

export function _encodeMuInstr(mnemonic, suffixes, operands, line) {
    if (MU_SYNC_MNEMONICS.has(mnemonic)) {
        return _encodeMuSync(mnemonic, operands, line);
    }
    return _encodeMuAsync(mnemonic, suffixes, operands, line);
}

function _encodeMuSync(mnemonic, operands, line) {
    if (mnemonic === "MSHAPE") return _encodeMshape(operands, line);
    if (mnemonic === "MFCLR") return [Op.MFCLR];
    if (mnemonic === "MWAIT") return [Op.MWAIT];
    if (mnemonic === "MFSTAT") {
        if (operands.length !== 1 || operands[0].tag !== TAG_REG) {
            throw new AsmError("MFSTAT requires one GPR operand", line);
        }
        if (operands[0].code > 3) {
            throw new AsmError("MFSTAT requires GPR A-D", line);
        }
        return [Op.MFSTAT, operands[0].code];
    }
    if (mnemonic === "MSET") return _encodeMset(operands, line);
    throw new AsmError(`Unknown MU sync instruction: ${mnemonic}`, line);
}

// MM=3, MN=4, MK=5
const _SHAPE_REG_CODES = [3, 4, 5];

function _encodeMshape(operands, line) {
    if (operands.length !== 3) {
        throw new AsmError("MSHAPE requires three immediates: M, N, K", line);
    }
    const out = [];
    for (let i = 0; i < 3; i++) {
        const op = operands[i];
        if (op.tag !== TAG_CONST) {
            throw new AsmError("MSHAPE operands must be numeric immediates", line);
        }
        const val = op.value;
        if (val < 0 || val > 65535) {
            throw new AsmError(`MSHAPE dimension out of range: ${val}`, line);
        }
        out.push(Op.MSET_IMM16, _SHAPE_REG_CODES[i], val & 0xff, (val >> 8) & 0xff);
    }
    return out;
}

const _MSET_BYTE_EXPR = new Set([TAG_CONST, TAG_LABEL, TAG_PAGE_LABEL, TAG_ADDR_LABEL]);

function _encodeMset(operands, line) {
    if (operands.length < 2) {
        throw new AsmError("MSET requires at least 2 operands", line);
    }
    if (operands[0].tag !== TAG_MU_REG) {
        throw new AsmError("MSET first operand must be an MU register", line);
    }
    const target = operands[0].code;

    // MSET reg, rH, rL — GPR pair
    if (operands.length === 3 && operands[1].tag === TAG_REG && operands[2].tag === TAG_REG) {
        const rh = operands[1].code;
        const rl = operands[2].code;
        if (rh > 3 || rl > 3) {
            throw new AsmError("MSET GPR pair requires A-D", line);
        }
        return [Op.MSET_GPR, target, (rh << 2) | rl];
    }

    // MSET reg, gpr — single GPR, zero-extended
    if (operands.length === 2 && operands[1].tag === TAG_REG) {
        const gpr = operands[1].code;
        if (gpr > 3) throw new AsmError("MSET single GPR requires A-D", line);
        return [Op.MSET_GPR, target, 0x10 | gpr];
    }

    // MSET reg, hi, lo — composite byte-expression pair
    if (operands.length === 3 && _MSET_BYTE_EXPR.has(operands[1].tag) && _MSET_BYTE_EXPR.has(operands[2].tag)) {
        const hiVal = operands[1].tag === TAG_CONST ? operands[1].value : 0;
        const loVal = operands[2].tag === TAG_CONST ? operands[2].value : 0;
        if (operands[1].tag === TAG_CONST && (hiVal < 0 || hiVal > 255)) {
            throw new AsmError(`MSET composite hi out of range: ${hiVal}`, line);
        }
        if (operands[2].tag === TAG_CONST && (loVal < 0 || loVal > 255)) {
            throw new AsmError(`MSET composite lo out of range: ${loVal}`, line);
        }
        return [Op.MSET_IMM16, target, loVal & 0xff, hiVal & 0xff];
    }

    // MSET reg, imm16
    if (operands.length === 2 && operands[1].tag === TAG_CONST) {
        const val = operands[1].value;
        if (val < 0 || val > 65535) {
            throw new AsmError(`MSET immediate must be 0-65535, got ${val}`, line);
        }
        return [Op.MSET_IMM16, target, val & 0xff, (val >> 8) & 0xff];
    }

    // MSET reg, label — full 16-bit address
    if (operands.length === 2 && operands[1].tag === TAG_LABEL) {
        return [Op.MSET_IMM16, target, 0, 0];
    }

    throw new AsmError("MSET does not support these operands", line);
}

function _encodeMuAsync(mnemonic, suffixes, operands, line) {
    const opMap = { MMUL: Op.MMUL, MMAD: Op.MMAD };
    const opcode = opMap[mnemonic];
    if (opcode === undefined) {
        throw new AsmError(`Unknown MU async instruction: ${mnemonic}`, line);
    }

    const fmtSuffix = suffixes[0] || null;
    const layoutSuffix = suffixes[1] || null;

    const fmt = _lookupSuffix(fmtSuffix, MU_SUFFIX_TO_FMT, "Invalid MU format suffix", line);
    const [aCol, bCol, cCol] = _resolveLayout(layoutSuffix, line);
    const mfmEnc = encodeMfm(fmt, aCol, bCol, cCol);

    const muRegs = operands.filter((op) => op.tag === TAG_MU_REG);
    if (muRegs.length !== 3) {
        throw new AsmError(`${mnemonic} requires three MU pointer operands (MC, MA, MB)`, line);
    }
    for (const r of muRegs) {
        if (r.code > 2) {
            throw new AsmError(`${mnemonic} operands must be MA/MB/MC (codes 0-2)`, line);
        }
    }
    return [opcode, mfmEnc, encodeVuRegs(muRegs[0].code, muRegs[1].code, muRegs[2].code)];
}

function _resolveLayout(suffix, line) {
    if (suffix === null) return [false, false, false];
    const s = suffix.toLowerCase();
    if (s.length !== 3 || !Array.from(s).every((c) => c === "r" || c === "c")) {
        throw new AsmError(`Invalid layout suffix '.${suffix}'; expected 3 chars r/c (e.g. 'rrr', 'rcr')`, line);
    }
    return [s[0] === "c", s[1] === "c", s[2] === "c"];
}
