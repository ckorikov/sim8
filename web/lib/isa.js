/**
 * ISA definitions: opcodes, registers, constants, and instruction table.
 * Generated data imported from _isa_tables.js (source: isa/isa.json).
 */

import { Op, ISA_DATA, ISA_FP_DATA, ISA_VU_DATA, FP_REG_DATA, MNEMONIC_ALIASES as _ALIASES } from "./_isa_tables.js";

export { Op };

// ── Registers ────────────────────────────────────────────────────

export const Reg = Object.freeze({
    A: 0,
    B: 1,
    C: 2,
    D: 3,
    SP: 4,
    DP: 5,
});

export const GPR_CODES = new Set([0, 1, 2, 3]);
export const ARITH_CODES = new Set([0, 1, 2, 3, 4]);
export const STACK_CODES = new Set([0, 1, 2, 3, 5]);

// ── Operand types ────────────────────────────────────────────────

export const OpType = Object.freeze({
    REG: "reg",
    REG_ARITH: "reg_arith",
    REG_GPR: "reg_gpr",
    REG_STACK: "reg_stack",
    IMM: "imm",
    MEM: "mem",
    REGADDR: "regaddr",
    FP_REG: "fp_reg",
    FP_IMM8: "fp_imm8",
    FP_IMM16: "fp_imm16",
});

const _OPTYPE_BYTES = { [OpType.FP_IMM16]: 2 };

// ── InstrDef ──────────────────────────────────────────────────────

function _buildInstrDef(op, mnemonic, format, cost = 1, fmtDep = false) {
    const size = 1 + format.reduce((s, ot) => s + (_OPTYPE_BYTES[ot] || 1), 0);
    return Object.freeze({ op, mnemonic, format: Object.freeze(format), cost, size, fmtDep });
}

// ── ISA builder ──────────────────────────────────────────────────

function _buildIsa(data) {
    return Object.freeze(
        data.map(([, opcode, mnemonic, operands, cost, fmtDep]) =>
            _buildInstrDef(opcode, mnemonic, operands, cost, fmtDep),
        ),
    );
}

// ── Integer ISA ──────────────────────────────────────────────────

export const ISA = _buildIsa(ISA_DATA);

// ── FP ISA ───────────────────────────────────────────────────────

export const ISA_FP = _buildIsa(ISA_FP_DATA);

// ── VU ISA ───────────────────────────────────────────────────────

export const ISA_VU = _buildIsa(ISA_VU_DATA);

// ── REGADDR encoding ─────────────────────────────────────────────

const _RA_REG_BITS = 3;
const _RA_REG_MASK = (1 << _RA_REG_BITS) - 1; // 0x07
const _RA_OFF_RANGE = 1 << (8 - _RA_REG_BITS); // 32
const _RA_OFF_MAX = (_RA_OFF_RANGE >> 1) - 1; // 15

export function encodeRegaddr(regCode, offset) {
    if (regCode < 0 || regCode > 5) {
        throw new RangeError(`Invalid register code: ${regCode}`);
    }
    if (offset < -16 || offset > 15) {
        throw new RangeError(`Offset out of range -16..+15: ${offset}`);
    }
    const offsetU = offset >= 0 ? offset : _RA_OFF_RANGE + offset;
    return (offsetU << _RA_REG_BITS) | regCode;
}

export function decodeRegaddr(encoded) {
    const regCode = encoded & _RA_REG_MASK;
    const offsetU = encoded >> _RA_REG_BITS;
    const offset = offsetU <= _RA_OFF_MAX ? offsetU : offsetU - _RA_OFF_RANGE;
    return [regCode, offset];
}

// ── Mnemonic aliases ─────────────────────────────────────────────

export const MNEMONIC_ALIASES = Object.freeze(Object.assign({}, _ALIASES));

// ── FP format constants ──────────────────────────────────────────

export const FP_FMT_F = 0;
export const FP_FMT_H = 1;
export const FP_FMT_BF = 2;
export const FP_FMT_O3 = 3;
export const FP_FMT_O2 = 4;
export const FP_FMT_N1 = 5;
export const FP_FMT_N2 = 6;

export const FP_FMT_WIDTH = Object.freeze({
    [FP_FMT_F]: 32,
    [FP_FMT_H]: 16,
    [FP_FMT_BF]: 16,
    [FP_FMT_O3]: 8,
    [FP_FMT_O2]: 8,
    [FP_FMT_N1]: 4,
    [FP_FMT_N2]: 4,
});

export const FP_FMT_MAX_POS = Object.freeze({
    [FP_FMT_F]: 0,
    [FP_FMT_H]: 1,
    [FP_FMT_BF]: 1,
    [FP_FMT_O3]: 3,
    [FP_FMT_O2]: 3,
    [FP_FMT_N1]: 7,
    [FP_FMT_N2]: 7,
});

export const FP_SUFFIX_TO_FMT = Object.freeze({
    F: FP_FMT_F,
    E8M23: FP_FMT_F,
    H: FP_FMT_H,
    E5M10: FP_FMT_H,
    BF: FP_FMT_BF,
    E8M7: FP_FMT_BF,
    O3: FP_FMT_O3,
    E4M3: FP_FMT_O3,
    O2: FP_FMT_O2,
    E5M2: FP_FMT_O2,
    N1: FP_FMT_N1,
    E2M1: FP_FMT_N1,
    N2: FP_FMT_N2,
    E1M2: FP_FMT_N2,
});

// ── FP registers ─────────────────────────────────────────────────

export const FP_REGISTERS = Object.freeze(
    Object.fromEntries(
        Object.entries(FP_REG_DATA).map(([name, [phys, pos, fmt, width]]) => [
            name,
            Object.freeze({ phys, pos, fmt, width }),
        ]),
    ),
);

// FP names forbidden as labels: real v2 registers + future-reserved names (spec §5.3).
// FC/FD = phys 2/3 full; FHE-FHH = phys 2/3 half; FQI-FQP = phys 2/3 quarter.
export const FORBIDDEN_FP_LABEL_NAMES = new Set([
    ...Object.keys(FP_REGISTERS),
    "FC",
    "FD",
    "FHE",
    "FHF",
    "FHG",
    "FHH",
    "FQI",
    "FQJ",
    "FQK",
    "FQL",
    "FQM",
    "FQN",
    "FQO",
    "FQP",
]);

export const FP_WIDTH_REGS = Object.freeze(
    Object.fromEntries(
        [32, 16, 8, 4].map((w) => [
            w,
            new Set(
                Object.entries(FP_REGISTERS)
                    .filter(([, r]) => r.width === w)
                    .map(([n]) => n),
            ),
        ]),
    ),
);

// ── FPM encoding ─────────────────────────────────────────────────

export function encodeFpm(phys, pos, fmt) {
    return (phys << 6) | (pos << 3) | fmt;
}

export function decodeFpm(fpm) {
    return [(fpm >> 6) & 0x03, (fpm >> 3) & 0x07, fpm & 0x07];
}

export function validateFpm(fpm) {
    const [phys, pos, fmt] = decodeFpm(fpm);
    if (phys > 1) return false;
    if (fmt >= 5) return false;
    return pos <= FP_FMT_MAX_POS[fmt];
}

// ── Derived lookup tables ────────────────────────────────────────

export const BY_CODE = Object.freeze(Object.fromEntries(ISA.map((i) => [i.op, i])));

export const BY_CODE_FP = Object.freeze(Object.fromEntries(ISA_FP.map((i) => [i.op, i])));

function _buildByMnemonic(table) {
    const m = {};
    for (const i of table) {
        (m[i.mnemonic] || (m[i.mnemonic] = [])).push(i);
    }
    return Object.freeze(Object.fromEntries(Object.entries(m).map(([k, v]) => [k, Object.freeze(v)])));
}

export const BY_MNEMONIC = _buildByMnemonic(ISA);
export const BY_MNEMONIC_FP = _buildByMnemonic(ISA_FP);

export const MNEMONICS = new Set([...Object.keys(BY_MNEMONIC), "DB"]);
export const MNEMONICS_FP = new Set(Object.keys(BY_MNEMONIC_FP));

export const FP_CONTROL_MNEMONICS = new Set(["FSTAT", "FCFG", "FSCFG", "FCLR"]);

// ── VU format constants ──────────────────────────────────────────

export const VU_FMT_U = 5;
export const VU_FMT_I = 6;

export const VU_SUFFIX_TO_FMT = Object.freeze({ F: 0, H: 1, BF: 2, O3: 3, O2: 4, U: 5, I: 6 });
export const VU_FMT_ELEM_SIZE = Object.freeze({ 0: 4, 1: 2, 2: 2, 3: 1, 4: 1, 5: 1, 6: 1 });

// ── VU mode constants ────────────────────────────────────────────

export const VU_MODE_VV = 0;
export const VU_MODE_VS = 1;
export const VU_MODE_VI = 2;
export const VU_MODE_R = 3;

export const VU_SUFFIX_TO_MODE = Object.freeze({ VV: 0, VS: 1, VI: 2, R: 3 });

// ── VU compare condition constants ───────────────────────────────

export const VU_CMP_EQ = 0;
export const VU_CMP_NE = 1;
export const VU_CMP_LT = 2;
export const VU_CMP_LE = 3;
export const VU_CMP_GT = 4;
export const VU_CMP_GE = 5;

export const VU_CMP_SUFFIX = Object.freeze({ EQ: 0, NE: 1, LT: 2, LE: 3, GT: 4, GE: 5 });

// ── VU window sizes ──────────────────────────────────────────────

// VU memory port: 8 bytes/tick → window size = 8 / elem_size elements
export const VU_WINDOW_SIZE = Object.freeze({ 1: 8, 2: 4, 4: 2 });

// ── VFM encoding/decoding ────────────────────────────────────────

export function encodeVfm(fmt, mode) {
    return (mode << 3) | fmt;
}

export function decodeVfm(vfm) {
    return [vfm & 7, (vfm >> 3) & 3, 0];
}

// ── VU register encoding/decoding ────────────────────────────────

export function encodeVuRegs(dst, src1, src2) {
    return (dst << 6) | (src1 << 4) | (src2 << 2);
}

export function decodeVuRegs(r) {
    return [(r >> 6) & 3, (r >> 4) & 3, (r >> 2) & 3];
}

// ── VU lookup tables ─────────────────────────────────────────────

export const BY_CODE_VU = Object.freeze(Object.fromEntries(ISA_VU.map((i) => [i.op, i])));
const BY_MNEMONIC_VU = _buildByMnemonic(ISA_VU);
export const MNEMONICS_VU = new Set(Object.keys(BY_MNEMONIC_VU));

// ── VU instruction categories ────────────────────────────────────

export const VU_SYNC_MNEMONICS = new Set(["VSET", "VFSTAT", "VFCLR", "VWAIT"]);

export const VU_ASYNC_OPS = new Set([
    Op.VADD,
    Op.VSUB,
    Op.VMUL,
    Op.VDIV,
    Op.VMAX,
    Op.VMIN,
    Op.VDOT,
    Op.VSQRT,
    Op.VNEG,
    Op.VABS,
    Op.VCMP,
    Op.VSEL,
    Op.VMOV,
    Op.VGATHER,
    Op.VSCATTER,
]);

export const VU_ARITH_OPS = new Set([Op.VADD, Op.VSUB, Op.VMUL, Op.VDIV, Op.VMAX, Op.VMIN]);
export const VU_UNARY_OPS = new Set([Op.VSQRT, Op.VNEG, Op.VABS]);
export const VU_VV_ONLY_OPS = new Set([Op.VDOT, Op.VCMP, Op.VSEL, Op.VGATHER, Op.VSCATTER]);
export const VU_INT_FMTS = new Set([VU_FMT_U, VU_FMT_I]);
