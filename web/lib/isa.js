/**
 * ISA definitions: opcodes, registers, constants, and instruction table.
 * Port of pysim8/src/pysim8/isa.py
 */

// ── Opcodes ──────────────────────────────────────────────────────

export const Op = Object.freeze({
    HLT: 0,

    // MOV (1-8)
    MOV_REG_REG: 1,
    MOV_REG_ADDR: 2,
    MOV_REG_REGADDR: 3,
    MOV_ADDR_REG: 4,
    MOV_REGADDR_REG: 5,
    MOV_REG_CONST: 6,
    MOV_ADDR_CONST: 7,
    MOV_REGADDR_CONST: 8,

    // ADD (10-13)
    ADD_REG_REG: 10,
    ADD_REG_REGADDR: 11,
    ADD_REG_ADDR: 12,
    ADD_REG_CONST: 13,

    // SUB (14-17)
    SUB_REG_REG: 14,
    SUB_REG_REGADDR: 15,
    SUB_REG_ADDR: 16,
    SUB_REG_CONST: 17,

    // INC / DEC (18-19)
    INC_REG: 18,
    DEC_REG: 19,

    // CMP (20-23)
    CMP_REG_REG: 20,
    CMP_REG_REGADDR: 21,
    CMP_REG_ADDR: 22,
    CMP_REG_CONST: 23,

    // JMP (30-31)
    JMP_REG: 30,
    JMP_ADDR: 31,

    // JC (32-33)
    JC_REG: 32,
    JC_ADDR: 33,

    // JNC (34-35)
    JNC_REG: 34,
    JNC_ADDR: 35,

    // JZ (36-37)
    JZ_REG: 36,
    JZ_ADDR: 37,

    // JNZ (38-39)
    JNZ_REG: 38,
    JNZ_ADDR: 39,

    // JA (40-41)
    JA_REG: 40,
    JA_ADDR: 41,

    // JNA (42-43)
    JNA_REG: 42,
    JNA_ADDR: 43,

    // PUSH (50-53)
    PUSH_REG: 50,
    PUSH_REGADDR: 51,
    PUSH_ADDR: 52,
    PUSH_CONST: 53,

    // POP (54)
    POP_REG: 54,

    // CALL (55-56)
    CALL_REG: 55,
    CALL_ADDR: 56,

    // RET (57)
    RET: 57,

    // MUL (60-63)
    MUL_REG: 60,
    MUL_REGADDR: 61,
    MUL_ADDR: 62,
    MUL_CONST: 63,

    // DIV (64-67)
    DIV_REG: 64,
    DIV_REGADDR: 65,
    DIV_ADDR: 66,
    DIV_CONST: 67,

    // AND (70-73)
    AND_REG_REG: 70,
    AND_REG_REGADDR: 71,
    AND_REG_ADDR: 72,
    AND_REG_CONST: 73,

    // OR (74-77)
    OR_REG_REG: 74,
    OR_REG_REGADDR: 75,
    OR_REG_ADDR: 76,
    OR_REG_CONST: 77,

    // XOR (78-81)
    XOR_REG_REG: 78,
    XOR_REG_REGADDR: 79,
    XOR_REG_ADDR: 80,
    XOR_REG_CONST: 81,

    // NOT (82)
    NOT_REG: 82,

    // SHL (90-93)
    SHL_REG_REG: 90,
    SHL_REG_REGADDR: 91,
    SHL_REG_ADDR: 92,
    SHL_REG_CONST: 93,

    // SHR (94-97)
    SHR_REG_REG: 94,
    SHR_REG_REGADDR: 95,
    SHR_REG_ADDR: 96,
    SHR_REG_CONST: 97,

    // FP -- FMOV (128-131)
    FMOV_FP_ADDR: 128,
    FMOV_FP_REGADDR: 129,
    FMOV_ADDR_FP: 130,
    FMOV_REGADDR_FP: 131,

    // FP -- FADD (132-133)
    FADD_FP_ADDR: 132,
    FADD_FP_REGADDR: 133,

    // FP -- FSUB (134-135)
    FSUB_FP_ADDR: 134,
    FSUB_FP_REGADDR: 135,

    // FP -- FMUL (136-137)
    FMUL_FP_ADDR: 136,
    FMUL_FP_REGADDR: 137,

    // FP -- FDIV (138-139)
    FDIV_FP_ADDR: 138,
    FDIV_FP_REGADDR: 139,

    // FP -- FCMP (140-141)
    FCMP_FP_ADDR: 140,
    FCMP_FP_REGADDR: 141,

    // FP -- FABS/FNEG/FSQRT (142-144)
    FABS_FP: 142,
    FNEG_FP: 143,
    FSQRT_FP: 144,

    // FP -- FMOV reg-reg (145)
    FMOV_RR: 145,

    // FP -- FCVT (146)
    FCVT_FP_FP: 146,

    // FP -- FITOF/FFTOI (147-148)
    FITOF_FP_GPR: 147,
    FFTOI_GPR_FP: 148,

    // FP -- Control (149-152)
    FSTAT_GPR: 149,
    FCFG_GPR: 150,
    FSCFG_GPR: 151,
    FCLR: 152,

    // FP -- Reg-Reg arithmetic (153-157)
    FADD_RR: 153,
    FSUB_RR: 154,
    FMUL_RR: 155,
    FDIV_RR: 156,
    FCMP_RR: 157,

    // FP -- FCLASS (158)
    FCLASS_GPR_FP: 158,

    // FP -- FMADD (159-160)
    FMADD_FP_FP_ADDR: 159,
    FMADD_FP_FP_REGADDR: 160,

    // FP -- FMOV immediate (161-162)
    FMOV_FP_IMM8: 161,
    FMOV_FP_IMM16: 162,
});

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

function instr(op, mnemonic, sig, cost = 1, formatDep = false) {
    const size = 1 + sig.reduce((s, ot) => s + (_OPTYPE_BYTES[ot] || 1), 0);
    return Object.freeze({ op, mnemonic, sig: Object.freeze(sig), cost, size, formatDep });
}

// Shorthands
const _REG = OpType.REG,
    _ARI = OpType.REG_ARITH,
    _GPR = OpType.REG_GPR,
    _STK = OpType.REG_STACK;
const _IMM = OpType.IMM,
    _MEM = OpType.MEM,
    _IADDR = OpType.REGADDR;
const _FP = OpType.FP_REG;

// ── Integer ISA ──────────────────────────────────────────────────

export const ISA = Object.freeze([
    // HLT (0)
    instr(Op.HLT, "HLT", [], 0),
    // MOV (1-8)
    instr(Op.MOV_REG_REG, "MOV", [_REG, _REG]),
    instr(Op.MOV_REG_ADDR, "MOV", [_REG, _MEM], 2),
    instr(Op.MOV_REG_REGADDR, "MOV", [_REG, _IADDR], 2),
    instr(Op.MOV_ADDR_REG, "MOV", [_MEM, _REG], 2),
    instr(Op.MOV_REGADDR_REG, "MOV", [_IADDR, _REG], 2),
    instr(Op.MOV_REG_CONST, "MOV", [_REG, _IMM]),
    instr(Op.MOV_ADDR_CONST, "MOV", [_MEM, _IMM], 2),
    instr(Op.MOV_REGADDR_CONST, "MOV", [_IADDR, _IMM], 2),
    // ADD (10-13)
    instr(Op.ADD_REG_REG, "ADD", [_ARI, _ARI]),
    instr(Op.ADD_REG_REGADDR, "ADD", [_ARI, _IADDR], 3),
    instr(Op.ADD_REG_ADDR, "ADD", [_ARI, _MEM], 3),
    instr(Op.ADD_REG_CONST, "ADD", [_ARI, _IMM]),
    // SUB (14-17)
    instr(Op.SUB_REG_REG, "SUB", [_ARI, _ARI]),
    instr(Op.SUB_REG_REGADDR, "SUB", [_ARI, _IADDR], 3),
    instr(Op.SUB_REG_ADDR, "SUB", [_ARI, _MEM], 3),
    instr(Op.SUB_REG_CONST, "SUB", [_ARI, _IMM]),
    // INC / DEC (18-19)
    instr(Op.INC_REG, "INC", [_ARI]),
    instr(Op.DEC_REG, "DEC", [_ARI]),
    // CMP (20-23)
    instr(Op.CMP_REG_REG, "CMP", [_ARI, _ARI]),
    instr(Op.CMP_REG_REGADDR, "CMP", [_ARI, _IADDR], 3),
    instr(Op.CMP_REG_ADDR, "CMP", [_ARI, _MEM], 3),
    instr(Op.CMP_REG_CONST, "CMP", [_ARI, _IMM]),
    // JMP (30-31)
    instr(Op.JMP_REG, "JMP", [_GPR]),
    instr(Op.JMP_ADDR, "JMP", [_IMM]),
    // JC (32-33)
    instr(Op.JC_REG, "JC", [_GPR]),
    instr(Op.JC_ADDR, "JC", [_IMM]),
    // JNC (34-35)
    instr(Op.JNC_REG, "JNC", [_GPR]),
    instr(Op.JNC_ADDR, "JNC", [_IMM]),
    // JZ (36-37)
    instr(Op.JZ_REG, "JZ", [_GPR]),
    instr(Op.JZ_ADDR, "JZ", [_IMM]),
    // JNZ (38-39)
    instr(Op.JNZ_REG, "JNZ", [_GPR]),
    instr(Op.JNZ_ADDR, "JNZ", [_IMM]),
    // JA (40-41)
    instr(Op.JA_REG, "JA", [_GPR]),
    instr(Op.JA_ADDR, "JA", [_IMM]),
    // JNA (42-43)
    instr(Op.JNA_REG, "JNA", [_GPR]),
    instr(Op.JNA_ADDR, "JNA", [_IMM]),
    // PUSH (50-53)
    instr(Op.PUSH_REG, "PUSH", [_STK], 2),
    instr(Op.PUSH_REGADDR, "PUSH", [_IADDR], 4),
    instr(Op.PUSH_ADDR, "PUSH", [_MEM], 4),
    instr(Op.PUSH_CONST, "PUSH", [_IMM], 2),
    // POP (54)
    instr(Op.POP_REG, "POP", [_STK], 2),
    // CALL (55-56)
    instr(Op.CALL_REG, "CALL", [_GPR], 2),
    instr(Op.CALL_ADDR, "CALL", [_IMM], 2),
    // RET (57)
    instr(Op.RET, "RET", [], 2),
    // MUL (60-63)
    instr(Op.MUL_REG, "MUL", [_GPR], 2),
    instr(Op.MUL_REGADDR, "MUL", [_IADDR], 4),
    instr(Op.MUL_ADDR, "MUL", [_MEM], 4),
    instr(Op.MUL_CONST, "MUL", [_IMM], 2),
    // DIV (64-67)
    instr(Op.DIV_REG, "DIV", [_GPR], 2),
    instr(Op.DIV_REGADDR, "DIV", [_IADDR], 4),
    instr(Op.DIV_ADDR, "DIV", [_MEM], 4),
    instr(Op.DIV_CONST, "DIV", [_IMM], 2),
    // AND (70-73)
    instr(Op.AND_REG_REG, "AND", [_GPR, _GPR]),
    instr(Op.AND_REG_REGADDR, "AND", [_GPR, _IADDR], 3),
    instr(Op.AND_REG_ADDR, "AND", [_GPR, _MEM], 3),
    instr(Op.AND_REG_CONST, "AND", [_GPR, _IMM]),
    // OR (74-77)
    instr(Op.OR_REG_REG, "OR", [_GPR, _GPR]),
    instr(Op.OR_REG_REGADDR, "OR", [_GPR, _IADDR], 3),
    instr(Op.OR_REG_ADDR, "OR", [_GPR, _MEM], 3),
    instr(Op.OR_REG_CONST, "OR", [_GPR, _IMM]),
    // XOR (78-81)
    instr(Op.XOR_REG_REG, "XOR", [_GPR, _GPR]),
    instr(Op.XOR_REG_REGADDR, "XOR", [_GPR, _IADDR], 3),
    instr(Op.XOR_REG_ADDR, "XOR", [_GPR, _MEM], 3),
    instr(Op.XOR_REG_CONST, "XOR", [_GPR, _IMM]),
    // NOT (82)
    instr(Op.NOT_REG, "NOT", [_GPR]),
    // SHL (90-93)
    instr(Op.SHL_REG_REG, "SHL", [_GPR, _GPR]),
    instr(Op.SHL_REG_REGADDR, "SHL", [_GPR, _IADDR], 3),
    instr(Op.SHL_REG_ADDR, "SHL", [_GPR, _MEM], 3),
    instr(Op.SHL_REG_CONST, "SHL", [_GPR, _IMM]),
    // SHR (94-97)
    instr(Op.SHR_REG_REG, "SHR", [_GPR, _GPR]),
    instr(Op.SHR_REG_REGADDR, "SHR", [_GPR, _IADDR], 3),
    instr(Op.SHR_REG_ADDR, "SHR", [_GPR, _MEM], 3),
    instr(Op.SHR_REG_CONST, "SHR", [_GPR, _IMM]),
]);

// ── FP ISA ───────────────────────────────────────────────────────

export const ISA_FP = Object.freeze([
    // FMOV (128-131) — format-dependent: mem(fmt) + overhead(0)
    instr(Op.FMOV_FP_ADDR, "FMOV", [_FP, _MEM], 0, true),
    instr(Op.FMOV_FP_REGADDR, "FMOV", [_FP, _IADDR], 0, true),
    instr(Op.FMOV_ADDR_FP, "FMOV", [_MEM, _FP], 0, true),
    instr(Op.FMOV_REGADDR_FP, "FMOV", [_IADDR, _FP], 0, true),
    // FADD (132-133) — format-dependent: mem(fmt) + overhead(2)
    instr(Op.FADD_FP_ADDR, "FADD", [_FP, _MEM], 2, true),
    instr(Op.FADD_FP_REGADDR, "FADD", [_FP, _IADDR], 2, true),
    // FSUB (134-135) — format-dependent: mem(fmt) + overhead(2)
    instr(Op.FSUB_FP_ADDR, "FSUB", [_FP, _MEM], 2, true),
    instr(Op.FSUB_FP_REGADDR, "FSUB", [_FP, _IADDR], 2, true),
    // FMUL (136-137) — format-dependent: mem(fmt) + overhead(2)
    instr(Op.FMUL_FP_ADDR, "FMUL", [_FP, _MEM], 2, true),
    instr(Op.FMUL_FP_REGADDR, "FMUL", [_FP, _IADDR], 2, true),
    // FDIV (138-139) — format-dependent: mem(fmt) + overhead(3)
    instr(Op.FDIV_FP_ADDR, "FDIV", [_FP, _MEM], 3, true),
    instr(Op.FDIV_FP_REGADDR, "FDIV", [_FP, _IADDR], 3, true),
    // FCMP (140-141) — format-dependent: mem(fmt) + overhead(2)
    instr(Op.FCMP_FP_ADDR, "FCMP", [_FP, _MEM], 2, true),
    instr(Op.FCMP_FP_REGADDR, "FCMP", [_FP, _IADDR], 2, true),
    // Unary (142-144)
    instr(Op.FABS_FP, "FABS", [_FP], 2),
    instr(Op.FNEG_FP, "FNEG", [_FP], 2),
    instr(Op.FSQRT_FP, "FSQRT", [_FP], 3),
    // FMOV reg-reg (145)
    instr(Op.FMOV_RR, "FMOV", [_FP, _FP], 1),
    // FCVT (146)
    instr(Op.FCVT_FP_FP, "FCVT", [_FP, _FP], 2),
    // FITOF (147)
    instr(Op.FITOF_FP_GPR, "FITOF", [_FP, _GPR], 2),
    // FFTOI (148) — assembly order: GPR, FP; encoding: [148, fpm, gpr]
    instr(Op.FFTOI_GPR_FP, "FFTOI", [_GPR, _FP], 2),
    // Control (149-152)
    instr(Op.FSTAT_GPR, "FSTAT", [_GPR], 1),
    instr(Op.FCFG_GPR, "FCFG", [_GPR], 1),
    instr(Op.FSCFG_GPR, "FSCFG", [_GPR], 1),
    instr(Op.FCLR, "FCLR", [], 1),
    // Reg-reg (153-157)
    instr(Op.FADD_RR, "FADD", [_FP, _FP], 2),
    instr(Op.FSUB_RR, "FSUB", [_FP, _FP], 2),
    instr(Op.FMUL_RR, "FMUL", [_FP, _FP], 2),
    instr(Op.FDIV_RR, "FDIV", [_FP, _FP], 3),
    instr(Op.FCMP_RR, "FCMP", [_FP, _FP], 2),
    // FCLASS (158)
    instr(Op.FCLASS_GPR_FP, "FCLASS", [_GPR, _FP], 1),
    // FMADD (159-160) — format-dependent: mem(fmt) + overhead(4)
    instr(Op.FMADD_FP_FP_ADDR, "FMADD", [_FP, _FP, _MEM], 4, true),
    instr(Op.FMADD_FP_FP_REGADDR, "FMADD", [_FP, _FP, _IADDR], 4, true),
    // FMOV immediate (161-162)
    instr(Op.FMOV_FP_IMM8, "FMOV", [_FP, OpType.FP_IMM8], 1),
    instr(Op.FMOV_FP_IMM16, "FMOV", [_FP, OpType.FP_IMM16], 1),
]);

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

export const MNEMONIC_ALIASES = Object.freeze({
    JB: "JC",
    JNAE: "JC",
    JNB: "JNC",
    JAE: "JNC",
    JE: "JZ",
    JNE: "JNZ",
    JNBE: "JA",
    JBE: "JNA",
    SAL: "SHL",
    SAR: "SHR",
});

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

function fpreg(phys, pos, fmt, width) {
    return Object.freeze({ phys, pos, fmt, width });
}

export const FP_REGISTERS = Object.freeze({
    // Physical register 0 (FA family)
    FA: fpreg(0, 0, FP_FMT_F, 32),
    FHA: fpreg(0, 0, FP_FMT_H, 16),
    FHB: fpreg(0, 1, FP_FMT_H, 16),
    FQA: fpreg(0, 0, FP_FMT_O3, 8),
    FQB: fpreg(0, 1, FP_FMT_O3, 8),
    FQC: fpreg(0, 2, FP_FMT_O3, 8),
    FQD: fpreg(0, 3, FP_FMT_O3, 8),
    FOA: fpreg(0, 0, FP_FMT_N1, 4),
    FOB: fpreg(0, 1, FP_FMT_N1, 4),
    FOC: fpreg(0, 2, FP_FMT_N1, 4),
    FOD: fpreg(0, 3, FP_FMT_N1, 4),
    FOE: fpreg(0, 4, FP_FMT_N1, 4),
    FOF: fpreg(0, 5, FP_FMT_N1, 4),
    FOG: fpreg(0, 6, FP_FMT_N1, 4),
    FOH: fpreg(0, 7, FP_FMT_N1, 4),
    // Physical register 1 (FB family)
    FB: fpreg(1, 0, FP_FMT_F, 32),
    FHC: fpreg(1, 0, FP_FMT_H, 16),
    FHD: fpreg(1, 1, FP_FMT_H, 16),
    FQE: fpreg(1, 0, FP_FMT_O3, 8),
    FQF: fpreg(1, 1, FP_FMT_O3, 8),
    FQG: fpreg(1, 2, FP_FMT_O3, 8),
    FQH: fpreg(1, 3, FP_FMT_O3, 8),
    FOI: fpreg(1, 0, FP_FMT_N1, 4),
    FOJ: fpreg(1, 1, FP_FMT_N1, 4),
    FOK: fpreg(1, 2, FP_FMT_N1, 4),
    FOL: fpreg(1, 3, FP_FMT_N1, 4),
    FOM: fpreg(1, 4, FP_FMT_N1, 4),
    FON: fpreg(1, 5, FP_FMT_N1, 4),
    FOO: fpreg(1, 6, FP_FMT_N1, 4),
    FOP: fpreg(1, 7, FP_FMT_N1, 4),
});

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

export const FP_WIDTH_REGS = Object.freeze({
    32: new Set(["FA", "FB"]),
    16: new Set(["FHA", "FHB", "FHC", "FHD"]),
    8: new Set(["FQA", "FQB", "FQC", "FQD", "FQE", "FQF", "FQG", "FQH"]),
    4: new Set([
        "FOA",
        "FOB",
        "FOC",
        "FOD",
        "FOE",
        "FOF",
        "FOG",
        "FOH",
        "FOI",
        "FOJ",
        "FOK",
        "FOL",
        "FOM",
        "FON",
        "FOO",
        "FOP",
    ]),
});

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
