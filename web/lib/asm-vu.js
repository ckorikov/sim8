/**
 * VU instruction encoding for the sim8 assembler.
 */

import {
    VU_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_MODE,
    VU_CMP_SUFFIX,
    VU_FMT_ELEM_SIZE,
    VU_MODE_VV,
    VU_MODE_VS,
    VU_MODE_VI,
    VU_MODE_R,
    VU_SYNC_MNEMONICS,
    encodeVfm,
    encodeVuRegs,
    encodeRegaddr,
} from "./isa.js";

import {
    Op,
    AsmError,
    TAG_REG,
    TAG_CONST,
    TAG_VU_REG,
    TAG_ADDR,
    TAG_REGADDR,
    TAG_ADDR_LABEL,
    TAG_LABEL,
    TAG_PAGE_LABEL,
} from "./asm-parse.js";

import { _lookupSuffix } from "./asm-core.js";

// ── VU instruction encoding ──────────────────────────────────────

export function _encodeVuInstr(mnemonic, suffixes, operands, line) {
    if (VU_SYNC_MNEMONICS.has(mnemonic)) {
        return _encodeVuSync(mnemonic, operands, line);
    }
    return _encodeVuAsync(mnemonic, suffixes, operands, line);
}

function _encodeVuSync(mnemonic, operands, line) {
    if (mnemonic === "VFCLR") return [Op.VFCLR];
    if (mnemonic === "VWAIT") return [Op.VWAIT];
    if (mnemonic === "VFSTAT") {
        if (operands.length !== 1 || operands[0].tag !== TAG_REG) {
            throw new AsmError("VFSTAT requires one GPR operand", line);
        }
        if (operands[0].code > 3) {
            throw new AsmError("VFSTAT requires GPR A-D", line);
        }
        return [Op.VFSTAT, operands[0].code];
    }
    if (mnemonic === "VSET") return _encodeVset(operands, line);
    throw new AsmError(`Unknown VU sync instruction: ${mnemonic}`, line);
}

const _VSET_BYTE_EXPR = new Set([TAG_CONST, TAG_LABEL, TAG_PAGE_LABEL, TAG_ADDR_LABEL]);

function _encodeVset(operands, line) {
    if (operands.length < 2) {
        throw new AsmError("VSET requires at least 2 operands", line);
    }
    if (operands[0].tag !== TAG_VU_REG) {
        throw new AsmError("VSET first operand must be a VU register", line);
    }
    const target = operands[0].code;

    // VSET vreg, rH, rL (opcode 164) — GPR pair; must come before composite check
    if (operands.length === 3 && operands[1].tag === TAG_REG && operands[2].tag === TAG_REG) {
        const rH = operands[1].code;
        const rL = operands[2].code;
        if (rH > 3 || rL > 3) {
            throw new AsmError("VSET GPR pair requires A-D", line);
        }
        return [Op.VSET_GPR, target, (rH << 2) | rL];
    }

    // VSET vreg, gpr (opcode 164) — single GPR, zero-extended to 16-bit (bit 4 flag)
    if (operands.length === 2 && operands[1].tag === TAG_REG) {
        const gpr = operands[1].code;
        if (gpr > 3) {
            throw new AsmError("VSET single GPR requires A-D", line);
        }
        return [Op.VSET_GPR, target, 0x10 | gpr];
    }

    // VSET vreg, hi, lo (opcode 163) — composite byte-expression pair
    // Accepted: number, bare label, {page-label}, [label] (resolves to offset)
    if (operands.length === 3 && _VSET_BYTE_EXPR.has(operands[1].tag) && _VSET_BYTE_EXPR.has(operands[2].tag)) {
        const hiVal = operands[1].tag === TAG_CONST ? operands[1].value : 0;
        const loVal = operands[2].tag === TAG_CONST ? operands[2].value : 0;
        if (operands[1].tag === TAG_CONST && (hiVal < 0 || hiVal > 255)) {
            throw new AsmError(`VSET composite hi operand out of range: ${hiVal}`, line);
        }
        if (operands[2].tag === TAG_CONST && (loVal < 0 || loVal > 255)) {
            throw new AsmError(`VSET composite lo operand out of range: ${loVal}`, line);
        }
        return [Op.VSET_IMM16, target, loVal & 0xff, hiVal & 0xff];
    }

    // VSET vreg, imm16 (opcode 163) — single numeric immediate, 0–65535
    if (operands.length === 2 && operands[1].tag === TAG_CONST) {
        const val = operands[1].value;
        if (val < 0 || val > 65535) {
            throw new AsmError(`VSET immediate must be 0-65535, got ${val}`, line);
        }
        return [Op.VSET_IMM16, target, val & 0xff, (val >> 8) & 0xff];
    }

    // VSET vreg, label (opcode 163) — full 16-bit address: lo=offset(label), hi=page(label), two patches emitted in pass 1
    if (operands.length === 2 && operands[1].tag === TAG_LABEL) {
        return [Op.VSET_IMM16, target, 0, 0];
    }

    // VSET vreg, [addr] / [label] (opcode 165) — read 16-bit LE from DP×256+addr
    if (operands.length === 2 && (operands[1].tag === TAG_ADDR || operands[1].tag === TAG_ADDR_LABEL)) {
        const addr = operands[1].tag === TAG_ADDR ? operands[1].value : 0;
        return [Op.VSET_MEM, target, addr];
    }

    // VSET vreg, [reg+-offset] (opcode 166)
    if (operands.length === 2 && operands[1].tag === TAG_REGADDR) {
        return [Op.VSET_MEMI, target, encodeRegaddr(operands[1].regCode, operands[1].offset)];
    }

    throw new AsmError("VSET does not support this operand(s)", line);
}

const _VU_MNEMONIC_TO_OP = {
    VADD: Op.VADD,
    VSUB: Op.VSUB,
    VMUL: Op.VMUL,
    VDIV: Op.VDIV,
    VMAX: Op.VMAX,
    VMIN: Op.VMIN,
    VDOT: Op.VDOT,
    VSQRT: Op.VSQRT,
    VNEG: Op.VNEG,
    VABS: Op.VABS,
    VCMP: Op.VCMP,
    VSEL: Op.VSEL,
    VMOV: Op.VMOV,
    VFILL: Op.VMOV,
    VGATHER: Op.VGATHER,
    VSCATTER: Op.VSCATTER,
};

const _VU_SINGLE_MODE = new Set(["VDOT", "VSQRT", "VNEG", "VABS", "VSEL", "VGATHER", "VSCATTER"]);

function _resolveVuModeCond(mnemonic, modeSuffix, operands, line) {
    if (mnemonic === "VCMP") {
        if (modeSuffix === null) throw new AsmError("VCMP requires a condition suffix", line);
        return [VU_MODE_VV, _lookupSuffix(modeSuffix, VU_CMP_SUFFIX, "Invalid VCMP condition", line)];
    }
    if (mnemonic === "VFILL") return [VU_MODE_VI, 0];
    if (_VU_SINGLE_MODE.has(mnemonic)) return [0, 0];

    // Explicit suffix takes priority
    if (modeSuffix !== null) return [_lookupSuffix(modeSuffix, VU_SUFFIX_TO_MODE, "Invalid VU mode suffix", line), 0];

    // Infer from operands
    const hasGpr = operands.some((op) => op.tag === TAG_REG);
    const hasImm = operands.some((op) => op.tag === TAG_CONST);
    const vuCount = _filterByTag(operands, TAG_VU_REG).length;
    if (hasGpr) return [VU_MODE_VS, 0];
    if (hasImm) return [VU_MODE_VI, 0];
    if (vuCount <= 2 && mnemonic !== "VMOV") return [VU_MODE_R, 0];
    return [VU_MODE_VV, 0];
}

function _resolveVuFmt(mnemonic, fmtSuffix, line) {
    if (fmtSuffix === null) throw new AsmError(`${mnemonic} requires a format suffix`, line);
    return _lookupSuffix(fmtSuffix, VU_SUFFIX_TO_FMT, "Invalid VU format suffix", line);
}

/** Filter operands by tag. */
export function _filterByTag(operands, tag) {
    return operands.filter((op) => op.tag === tag);
}

function _encodeVuRegsFromOperands(operands, mnemonic, mode, line) {
    const vuRegs = _filterByTag(operands, TAG_VU_REG);
    if (vuRegs.length === 0) {
        throw new AsmError(`${mnemonic} requires VU register operands`, line);
    }
    for (const r of vuRegs) {
        if (r.code > 3) {
            throw new AsmError("Async VU operands must be pointer registers (VA-VM)", line);
        }
    }
    const dst = vuRegs[0].code;
    const src1 = vuRegs.length > 1 ? vuRegs[1].code : 0;
    let src2;
    if (mode === VU_MODE_VS) {
        const gprOps = _filterByTag(operands, TAG_REG);
        if (gprOps.length === 0) {
            throw new AsmError(`${mnemonic} broadcast requires a GPR operand (A-D)`, line);
        }
        if (gprOps[0].code > 3) {
            throw new AsmError("Broadcast GPR must be A-D", line);
        }
        src2 = gprOps[0].code;
    } else {
        src2 = vuRegs.length > 2 ? vuRegs[2].code : 0;
    }
    return encodeVuRegs(dst, src1, src2);
}

function _encodeVuAsync(mnemonic, suffixes, operands, line) {
    const opcode = _VU_MNEMONIC_TO_OP[mnemonic];
    if (opcode === undefined) {
        throw new AsmError(`Unknown VU async instruction: ${mnemonic}`, line);
    }

    const fmtSuffix = suffixes[0] || null;
    const modeSuffix = suffixes[1] || null;

    const fmt = _resolveVuFmt(mnemonic, fmtSuffix, line);
    const [mode, cond] = _resolveVuModeCond(mnemonic, modeSuffix, operands, line);

    // GPR broadcast restricted to byte formats
    if (mode === VU_MODE_VS && (VU_FMT_ELEM_SIZE[fmt] || 1) > 1) {
        throw new AsmError(`GPR broadcast only for byte formats (U/I/O3/O2), not .${fmtSuffix}`, line);
    }

    const regs = _encodeVuRegsFromOperands(operands, mnemonic, mode, line);
    const result = [opcode, encodeVfm(fmt, mode), regs];
    if (mnemonic === "VCMP") result.push(cond);

    if (mode === VU_MODE_VI) {
        const immOps = _filterByTag(operands, TAG_CONST);
        if (immOps.length === 0) {
            throw new AsmError(`${mnemonic} requires an immediate operand`, line);
        }
        const immVal = immOps[0].value;
        const elemSize = VU_FMT_ELEM_SIZE[fmt] || 1;
        for (let i = 0; i < elemSize; i++) {
            result.push((immVal >> (8 * i)) & 0xff);
        }
    }

    return result;
}
