(() => {
  var __create = Object.create;
  var __defProp = Object.defineProperty;
  var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
  var __getOwnPropNames = Object.getOwnPropertyNames;
  var __getProtoOf = Object.getPrototypeOf;
  var __hasOwnProp = Object.prototype.hasOwnProperty;
  var __require = /* @__PURE__ */ ((x) => typeof require !== "undefined" ? require : typeof Proxy !== "undefined" ? new Proxy(x, {
    get: (a, b) => (typeof require !== "undefined" ? require : a)[b]
  }) : x)(function(x) {
    if (typeof require !== "undefined") return require.apply(this, arguments);
    throw Error('Dynamic require of "' + x + '" is not supported');
  });
  var __copyProps = (to, from, except, desc) => {
    if (from && typeof from === "object" || typeof from === "function") {
      for (let key of __getOwnPropNames(from))
        if (!__hasOwnProp.call(to, key) && key !== except)
          __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
    }
    return to;
  };
  var __toESM = (mod, isNodeMode, target) => (target = mod != null ? __create(__getProtoOf(mod)) : {}, __copyProps(
    // If the importer is in node compatibility mode or this is not an ESM
    // file that has been converted to a CommonJS file using a Babel-
    // compatible transform (i.e. "__esModule" has not been set), then set
    // "default" to the CommonJS "module.exports" for node compatibility.
    isNodeMode || !mod || !mod.__esModule ? __defProp(target, "default", { value: mod, enumerable: true }) : target,
    mod
  ));

  // isa.js
  var Op = Object.freeze({
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
    FMOV_FP_IMM16: 162
  });
  var Reg = Object.freeze({
    A: 0,
    B: 1,
    C: 2,
    D: 3,
    SP: 4,
    DP: 5
  });
  var REGISTERS = Object.freeze({
    A: 0,
    B: 1,
    C: 2,
    D: 3,
    SP: 4,
    DP: 5
  });
  var GPR_CODES = /* @__PURE__ */ new Set([0, 1, 2, 3]);
  var STACK_CODES = /* @__PURE__ */ new Set([0, 1, 2, 3, 4]);
  var OpType = Object.freeze({
    REG: "reg",
    REG_STACK: "reg_stack",
    REG_GPR: "reg_gpr",
    IMM: "imm",
    MEM: "mem",
    REGADDR: "regaddr",
    FP_REG: "fp_reg",
    FP_IMM8: "fp_imm8",
    FP_IMM16: "fp_imm16"
  });
  var _OPTYPE_BYTES = { [OpType.FP_IMM16]: 2 };
  function insn(op, mnemonic, sig, cost = 1) {
    const size = 1 + sig.reduce((s, ot) => s + (_OPTYPE_BYTES[ot] || 1), 0);
    return Object.freeze({ op, mnemonic, sig: Object.freeze(sig), cost, size });
  }
  var _REG = OpType.REG;
  var _STK = OpType.REG_STACK;
  var _GPR = OpType.REG_GPR;
  var _IMM = OpType.IMM;
  var _MEM = OpType.MEM;
  var _IADDR = OpType.REGADDR;
  var _FP = OpType.FP_REG;
  var ISA = Object.freeze([
    // HLT (0)
    insn(Op.HLT, "HLT", [], 0),
    // MOV (1-8)
    insn(Op.MOV_REG_REG, "MOV", [_REG, _REG]),
    insn(Op.MOV_REG_ADDR, "MOV", [_REG, _MEM], 2),
    insn(Op.MOV_REG_REGADDR, "MOV", [_REG, _IADDR], 2),
    insn(Op.MOV_ADDR_REG, "MOV", [_MEM, _REG], 2),
    insn(Op.MOV_REGADDR_REG, "MOV", [_IADDR, _REG], 2),
    insn(Op.MOV_REG_CONST, "MOV", [_REG, _IMM]),
    insn(Op.MOV_ADDR_CONST, "MOV", [_MEM, _IMM], 2),
    insn(Op.MOV_REGADDR_CONST, "MOV", [_IADDR, _IMM], 2),
    // ADD (10-13)
    insn(Op.ADD_REG_REG, "ADD", [_STK, _STK]),
    insn(Op.ADD_REG_REGADDR, "ADD", [_STK, _IADDR], 3),
    insn(Op.ADD_REG_ADDR, "ADD", [_STK, _MEM], 3),
    insn(Op.ADD_REG_CONST, "ADD", [_STK, _IMM]),
    // SUB (14-17)
    insn(Op.SUB_REG_REG, "SUB", [_STK, _STK]),
    insn(Op.SUB_REG_REGADDR, "SUB", [_STK, _IADDR], 3),
    insn(Op.SUB_REG_ADDR, "SUB", [_STK, _MEM], 3),
    insn(Op.SUB_REG_CONST, "SUB", [_STK, _IMM]),
    // INC / DEC (18-19)
    insn(Op.INC_REG, "INC", [_STK]),
    insn(Op.DEC_REG, "DEC", [_STK]),
    // CMP (20-23)
    insn(Op.CMP_REG_REG, "CMP", [_STK, _STK]),
    insn(Op.CMP_REG_REGADDR, "CMP", [_STK, _IADDR], 3),
    insn(Op.CMP_REG_ADDR, "CMP", [_STK, _MEM], 3),
    insn(Op.CMP_REG_CONST, "CMP", [_STK, _IMM]),
    // JMP (30-31)
    insn(Op.JMP_REG, "JMP", [_GPR]),
    insn(Op.JMP_ADDR, "JMP", [_IMM]),
    // JC (32-33)
    insn(Op.JC_REG, "JC", [_GPR]),
    insn(Op.JC_ADDR, "JC", [_IMM]),
    // JNC (34-35)
    insn(Op.JNC_REG, "JNC", [_GPR]),
    insn(Op.JNC_ADDR, "JNC", [_IMM]),
    // JZ (36-37)
    insn(Op.JZ_REG, "JZ", [_GPR]),
    insn(Op.JZ_ADDR, "JZ", [_IMM]),
    // JNZ (38-39)
    insn(Op.JNZ_REG, "JNZ", [_GPR]),
    insn(Op.JNZ_ADDR, "JNZ", [_IMM]),
    // JA (40-41)
    insn(Op.JA_REG, "JA", [_GPR]),
    insn(Op.JA_ADDR, "JA", [_IMM]),
    // JNA (42-43)
    insn(Op.JNA_REG, "JNA", [_GPR]),
    insn(Op.JNA_ADDR, "JNA", [_IMM]),
    // PUSH (50-53)
    insn(Op.PUSH_REG, "PUSH", [_GPR], 2),
    insn(Op.PUSH_REGADDR, "PUSH", [_IADDR], 4),
    insn(Op.PUSH_ADDR, "PUSH", [_MEM], 4),
    insn(Op.PUSH_CONST, "PUSH", [_IMM], 2),
    // POP (54)
    insn(Op.POP_REG, "POP", [_GPR], 2),
    // CALL (55-56)
    insn(Op.CALL_REG, "CALL", [_GPR], 2),
    insn(Op.CALL_ADDR, "CALL", [_IMM], 2),
    // RET (57)
    insn(Op.RET, "RET", [], 2),
    // MUL (60-63)
    insn(Op.MUL_REG, "MUL", [_GPR], 2),
    insn(Op.MUL_REGADDR, "MUL", [_IADDR], 4),
    insn(Op.MUL_ADDR, "MUL", [_MEM], 4),
    insn(Op.MUL_CONST, "MUL", [_IMM], 2),
    // DIV (64-67)
    insn(Op.DIV_REG, "DIV", [_GPR], 2),
    insn(Op.DIV_REGADDR, "DIV", [_IADDR], 4),
    insn(Op.DIV_ADDR, "DIV", [_MEM], 4),
    insn(Op.DIV_CONST, "DIV", [_IMM], 2),
    // AND (70-73)
    insn(Op.AND_REG_REG, "AND", [_GPR, _GPR]),
    insn(Op.AND_REG_REGADDR, "AND", [_GPR, _IADDR], 3),
    insn(Op.AND_REG_ADDR, "AND", [_GPR, _MEM], 3),
    insn(Op.AND_REG_CONST, "AND", [_GPR, _IMM]),
    // OR (74-77)
    insn(Op.OR_REG_REG, "OR", [_GPR, _GPR]),
    insn(Op.OR_REG_REGADDR, "OR", [_GPR, _IADDR], 3),
    insn(Op.OR_REG_ADDR, "OR", [_GPR, _MEM], 3),
    insn(Op.OR_REG_CONST, "OR", [_GPR, _IMM]),
    // XOR (78-81)
    insn(Op.XOR_REG_REG, "XOR", [_GPR, _GPR]),
    insn(Op.XOR_REG_REGADDR, "XOR", [_GPR, _IADDR], 3),
    insn(Op.XOR_REG_ADDR, "XOR", [_GPR, _MEM], 3),
    insn(Op.XOR_REG_CONST, "XOR", [_GPR, _IMM]),
    // NOT (82)
    insn(Op.NOT_REG, "NOT", [_GPR]),
    // SHL (90-93)
    insn(Op.SHL_REG_REG, "SHL", [_GPR, _GPR]),
    insn(Op.SHL_REG_REGADDR, "SHL", [_GPR, _IADDR], 3),
    insn(Op.SHL_REG_ADDR, "SHL", [_GPR, _MEM], 3),
    insn(Op.SHL_REG_CONST, "SHL", [_GPR, _IMM]),
    // SHR (94-97)
    insn(Op.SHR_REG_REG, "SHR", [_GPR, _GPR]),
    insn(Op.SHR_REG_REGADDR, "SHR", [_GPR, _IADDR], 3),
    insn(Op.SHR_REG_ADDR, "SHR", [_GPR, _MEM], 3),
    insn(Op.SHR_REG_CONST, "SHR", [_GPR, _IMM])
  ]);
  var ISA_FP = Object.freeze([
    // FMOV (128-131)
    insn(Op.FMOV_FP_ADDR, "FMOV", [_FP, _MEM], 2),
    insn(Op.FMOV_FP_REGADDR, "FMOV", [_FP, _IADDR], 2),
    insn(Op.FMOV_ADDR_FP, "FMOV", [_MEM, _FP], 2),
    insn(Op.FMOV_REGADDR_FP, "FMOV", [_IADDR, _FP], 2),
    // FADD (132-133)
    insn(Op.FADD_FP_ADDR, "FADD", [_FP, _MEM], 5),
    insn(Op.FADD_FP_REGADDR, "FADD", [_FP, _IADDR], 5),
    // FSUB (134-135)
    insn(Op.FSUB_FP_ADDR, "FSUB", [_FP, _MEM], 5),
    insn(Op.FSUB_FP_REGADDR, "FSUB", [_FP, _IADDR], 5),
    // FMUL (136-137)
    insn(Op.FMUL_FP_ADDR, "FMUL", [_FP, _MEM], 5),
    insn(Op.FMUL_FP_REGADDR, "FMUL", [_FP, _IADDR], 5),
    // FDIV (138-139)
    insn(Op.FDIV_FP_ADDR, "FDIV", [_FP, _MEM], 5),
    insn(Op.FDIV_FP_REGADDR, "FDIV", [_FP, _IADDR], 5),
    // FCMP (140-141)
    insn(Op.FCMP_FP_ADDR, "FCMP", [_FP, _MEM], 5),
    insn(Op.FCMP_FP_REGADDR, "FCMP", [_FP, _IADDR], 5),
    // Unary (142-144)
    insn(Op.FABS_FP, "FABS", [_FP], 3),
    insn(Op.FNEG_FP, "FNEG", [_FP], 3),
    insn(Op.FSQRT_FP, "FSQRT", [_FP], 4),
    // FMOV reg-reg (145)
    insn(Op.FMOV_RR, "FMOV", [_FP, _FP], 1),
    // FCVT (146)
    insn(Op.FCVT_FP_FP, "FCVT", [_FP, _FP], 3),
    // FITOF (147)
    insn(Op.FITOF_FP_GPR, "FITOF", [_FP, _GPR], 3),
    // FFTOI (148) — assembly order: GPR, FP; encoding: [148, fpm, gpr]
    insn(Op.FFTOI_GPR_FP, "FFTOI", [_GPR, _FP], 3),
    // Control (149-152)
    insn(Op.FSTAT_GPR, "FSTAT", [_GPR], 1),
    insn(Op.FCFG_GPR, "FCFG", [_GPR], 1),
    insn(Op.FSCFG_GPR, "FSCFG", [_GPR], 1),
    insn(Op.FCLR, "FCLR", [], 1),
    // Reg-reg (153-157)
    insn(Op.FADD_RR, "FADD", [_FP, _FP], 3),
    insn(Op.FSUB_RR, "FSUB", [_FP, _FP], 3),
    insn(Op.FMUL_RR, "FMUL", [_FP, _FP], 3),
    insn(Op.FDIV_RR, "FDIV", [_FP, _FP], 3),
    insn(Op.FCMP_RR, "FCMP", [_FP, _FP], 3),
    // FCLASS (158)
    insn(Op.FCLASS_GPR_FP, "FCLASS", [_GPR, _FP], 2),
    // FMADD (159-160)
    insn(Op.FMADD_FP_FP_ADDR, "FMADD", [_FP, _FP, _MEM], 6),
    insn(Op.FMADD_FP_FP_REGADDR, "FMADD", [_FP, _FP, _IADDR], 6),
    // FMOV immediate (161-162)
    insn(Op.FMOV_FP_IMM8, "FMOV", [_FP, OpType.FP_IMM8], 1),
    insn(Op.FMOV_FP_IMM16, "FMOV", [_FP, OpType.FP_IMM16], 1)
  ]);
  var _RA_REG_BITS = 3;
  var _RA_REG_MASK = (1 << _RA_REG_BITS) - 1;
  var _RA_OFF_RANGE = 1 << 8 - _RA_REG_BITS;
  var _RA_OFF_MAX = (_RA_OFF_RANGE >> 1) - 1;
  function encodeRegaddr(regCode, offset) {
    if (regCode < 0 || regCode > 5) {
      throw new RangeError(`Invalid register code: ${regCode}`);
    }
    if (offset < -16 || offset > 15) {
      throw new RangeError(`Offset out of range -16..+15: ${offset}`);
    }
    const offsetU = offset >= 0 ? offset : _RA_OFF_RANGE + offset;
    return offsetU << _RA_REG_BITS | regCode;
  }
  function decodeRegaddr(encoded) {
    const regCode = encoded & _RA_REG_MASK;
    const offsetU = encoded >> _RA_REG_BITS;
    const offset = offsetU <= _RA_OFF_MAX ? offsetU : offsetU - _RA_OFF_RANGE;
    return [regCode, offset];
  }
  var MNEMONIC_ALIASES = Object.freeze({
    JB: "JC",
    JNAE: "JC",
    JNB: "JNC",
    JAE: "JNC",
    JE: "JZ",
    JNE: "JNZ",
    JNBE: "JA",
    JBE: "JNA",
    SAL: "SHL",
    SAR: "SHR"
  });
  var FP_FMT_F = 0;
  var FP_FMT_H = 1;
  var FP_FMT_BF = 2;
  var FP_FMT_O3 = 3;
  var FP_FMT_O2 = 4;
  var FP_FMT_N1 = 5;
  var FP_FMT_N2 = 6;
  var FP_FMT_WIDTH = Object.freeze({
    [FP_FMT_F]: 32,
    [FP_FMT_H]: 16,
    [FP_FMT_BF]: 16,
    [FP_FMT_O3]: 8,
    [FP_FMT_O2]: 8,
    [FP_FMT_N1]: 4,
    [FP_FMT_N2]: 4
  });
  var FP_FMT_MAX_POS = Object.freeze({
    [FP_FMT_F]: 0,
    [FP_FMT_H]: 1,
    [FP_FMT_BF]: 1,
    [FP_FMT_O3]: 3,
    [FP_FMT_O2]: 3,
    [FP_FMT_N1]: 7,
    [FP_FMT_N2]: 7
  });
  var FP_SUFFIX_TO_FMT = Object.freeze({
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
    E1M2: FP_FMT_N2
  });
  var FP_DB_SUFFIX_TO_FMT = FP_SUFFIX_TO_FMT;
  function fpreg(phys, pos, fmt, width) {
    return Object.freeze({ phys, pos, fmt, width });
  }
  var FP_REGISTERS = Object.freeze({
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
    FOP: fpreg(1, 7, FP_FMT_N1, 4)
  });
  var FP_WIDTH_REGS = Object.freeze({
    32: /* @__PURE__ */ new Set(["FA", "FB"]),
    16: /* @__PURE__ */ new Set(["FHA", "FHB", "FHC", "FHD"]),
    8: /* @__PURE__ */ new Set(["FQA", "FQB", "FQC", "FQD", "FQE", "FQF", "FQG", "FQH"]),
    4: /* @__PURE__ */ new Set([
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
      "FOP"
    ])
  });
  function encodeFpm(phys, pos, fmt) {
    return phys << 6 | pos << 3 | fmt;
  }
  function decodeFpm(fpm) {
    return [fpm >> 6 & 3, fpm >> 3 & 7, fpm & 7];
  }
  function validateFpm(fpm) {
    const [phys, pos, fmt] = decodeFpm(fpm);
    if (phys > 1) return false;
    if (fmt >= 5) return false;
    return pos <= FP_FMT_MAX_POS[fmt];
  }
  var BY_CODE = Object.freeze(
    Object.fromEntries(ISA.map((i) => [i.op, i]))
  );
  var BY_CODE_FP = Object.freeze(
    Object.fromEntries(ISA_FP.map((i) => [i.op, i]))
  );
  function _buildByMnemonic(table) {
    const m = {};
    for (const i of table) {
      (m[i.mnemonic] || (m[i.mnemonic] = [])).push(i);
    }
    return Object.freeze(Object.fromEntries(
      Object.entries(m).map(([k, v]) => [k, Object.freeze(v)])
    ));
  }
  var BY_MNEMONIC = _buildByMnemonic(ISA);
  var BY_MNEMONIC_FP = _buildByMnemonic(ISA_FP);
  var MNEMONICS = /* @__PURE__ */ new Set([...Object.keys(BY_MNEMONIC), "DB"]);
  var MNEMONICS_FP = new Set(Object.keys(BY_MNEMONIC_FP));
  var FP_CONTROL_MNEMONICS = /* @__PURE__ */ new Set(["FSTAT", "FCFG", "FSCFG", "FCLR"]);

  // fp.js
  var RoundingMode = Object.freeze({
    RNE: 0,
    // Round to Nearest, ties to Even
    RTZ: 1,
    // Round toward Zero
    RDN: 2,
    // Round toward -Inf
    RUP: 3
    // Round toward +Inf
  });
  var NO_EXC = Object.freeze({
    invalid: false,
    divZero: false,
    overflow: false,
    underflow: false,
    inexact: false
  });
  function exc({
    invalid = false,
    divZero = false,
    overflow = false,
    underflow = false,
    inexact = false
  } = {}) {
    return Object.freeze({ invalid, divZero, overflow, underflow, inexact });
  }
  function excReplace(base, overrides) {
    return exc({
      invalid: overrides.invalid !== void 0 ? overrides.invalid : base.invalid,
      divZero: overrides.divZero !== void 0 ? overrides.divZero : base.divZero,
      overflow: overrides.overflow !== void 0 ? overrides.overflow : base.overflow,
      underflow: overrides.underflow !== void 0 ? overrides.underflow : base.underflow,
      inexact: overrides.inexact !== void 0 ? overrides.inexact : base.inexact
    });
  }
  var _f32buf = new ArrayBuffer(4);
  var _f32arr = new Float32Array(_f32buf);
  var _u32arr = new Uint32Array(_f32buf);
  var _f64buf = new ArrayBuffer(8);
  var _f64view = new Float64Array(_f64buf);
  var _i64view = new BigInt64Array(_f64buf);
  function nextafter(from, to) {
    if (Number.isNaN(from) || Number.isNaN(to)) return NaN;
    if (from === to) return to;
    if (from === 0) {
      return to > 0 ? 5e-324 : -5e-324;
    }
    _f64view[0] = from;
    if (from < to === from > 0) {
      _i64view[0] += 1n;
    } else {
      _i64view[0] -= 1n;
    }
    return _f64view[0];
  }
  function copysign(x, y) {
    const ax = Math.abs(x);
    return y < 0 || Object.is(y, -0) ? -ax : ax;
  }
  var _MIN_NORMAL_F32 = 11754943508222875e-54;
  var _MIN_NORMAL_F16 = 6103515625e-14;
  var _OVERFLOW_THRESH_F32 = 34028235677973366e22;
  var _OVERFLOW_THRESH_F16 = 65520;
  function encodeFloat32(value, rm = 0) {
    if (Number.isNaN(value) || !Number.isFinite(value) || value === 0) {
      _f32arr[0] = value;
      const data2 = new Uint8Array(4);
      data2[0] = _u32arr[0] & 255;
      data2[1] = _u32arr[0] >> 8 & 255;
      data2[2] = _u32arr[0] >> 16 & 255;
      data2[3] = _u32arr[0] >> 24 & 255;
      return { data: data2, exc: NO_EXC };
    }
    if (rm !== RoundingMode.RNE) {
      return _encodeIeeeDirected(value, 8, 23, 127, rm);
    }
    if (Math.abs(value) >= _OVERFLOW_THRESH_F32) {
      const sign = value < 0 ? -1 : 1;
      _f32arr[0] = sign * Infinity;
      const data2 = new Uint8Array(4);
      data2[0] = _u32arr[0] & 255;
      data2[1] = _u32arr[0] >> 8 & 255;
      data2[2] = _u32arr[0] >> 16 & 255;
      data2[3] = _u32arr[0] >> 24 & 255;
      return { data: data2, exc: exc({ overflow: true, inexact: true }) };
    }
    _f32arr[0] = value;
    const f32Bits = _u32arr[0];
    const rt = _f32arr[0];
    const data = new Uint8Array(4);
    data[0] = f32Bits & 255;
    data[1] = f32Bits >> 8 & 255;
    data[2] = f32Bits >> 16 & 255;
    data[3] = f32Bits >> 24 & 255;
    const overflow = !Number.isFinite(rt) && Number.isFinite(value);
    const expBits = f32Bits >>> 23 & 255;
    const isSub = expBits === 0 && (f32Bits & 8388607) !== 0;
    const flushedToZero = rt === 0 && value !== 0;
    const exactSubnormal = 0 < Math.abs(value) && Math.abs(value) < _MIN_NORMAL_F32;
    const underflow = isSub || flushedToZero || exactSubnormal;
    const inexact = rt !== value;
    return {
      data,
      exc: exc({ overflow, underflow, inexact: inexact || overflow })
    };
  }
  function decodeFloat32(data) {
    _u32arr[0] = data[0] | data[1] << 8 | data[2] << 16 | data[3] << 24 >>> 0;
    return _f32arr[0];
  }
  function _encodeFloat16Rne(value) {
    _f32arr[0] = value;
    const f32Bits = _u32arr[0];
    const f32Sign = f32Bits >>> 31 & 1;
    const f32Exp = f32Bits >>> 23 & 255;
    const f32Mant = f32Bits & 8388607;
    let f16Sign = f32Sign;
    let f16Exp;
    let f16Mant;
    const unbiasedExp = f32Exp - 127;
    if (f32Exp === 0) {
      f16Exp = 0;
      f16Mant = 0;
    } else if (f32Exp === 255) {
      f16Exp = 31;
      f16Mant = f32Mant !== 0 ? 512 : 0;
    } else if (unbiasedExp < -24) {
      f16Exp = 0;
      f16Mant = 0;
    } else if (unbiasedExp < -14) {
      f16Exp = 0;
      const fullMant = 1 << 23 | f32Mant;
      const shiftAmount = -1 - unbiasedExp + 13;
      const shift = -1 - unbiasedExp;
      const shifted = fullMant >> shift;
      const remainder = fullMant & (1 << shift) - 1;
      const halfway = 1 << shift - 1;
      if (remainder > halfway) {
        f16Mant = shifted + 1;
      } else if (remainder === halfway) {
        f16Mant = shifted & 1 ? shifted + 1 : shifted;
      } else {
        f16Mant = shifted;
      }
      if (f16Mant >= 1 << 10) {
        f16Exp = 1;
        f16Mant = 0;
      } else {
        f16Mant &= 1023;
      }
    } else if (unbiasedExp > 15) {
      f16Exp = 31;
      f16Mant = 0;
    } else {
      f16Exp = unbiasedExp + 15;
      const dropped = f32Mant & 8191;
      const halfway = 4096;
      f16Mant = f32Mant >> 13;
      if (dropped > halfway) {
        f16Mant += 1;
      } else if (dropped === halfway) {
        if (f16Mant & 1) {
          f16Mant += 1;
        }
      }
      if (f16Mant > 1023) {
        f16Mant = 0;
        f16Exp += 1;
        if (f16Exp >= 31) {
          f16Exp = 31;
          f16Mant = 0;
        }
      }
    }
    return f16Sign << 15 | f16Exp << 10 | f16Mant;
  }
  function encodeFloat16(value, rm = 0) {
    if (Number.isNaN(value)) {
      const data2 = new Uint8Array(2);
      data2[0] = 0;
      data2[1] = 126;
      return { data: data2, exc: NO_EXC };
    }
    if (!Number.isFinite(value)) {
      const bits = value > 0 ? 31744 : 64512;
      const data2 = new Uint8Array(2);
      data2[0] = bits & 255;
      data2[1] = bits >> 8 & 255;
      return { data: data2, exc: NO_EXC };
    }
    if (value === 0) {
      const isNeg = Object.is(value, -0);
      const bits = isNeg ? 32768 : 0;
      const data2 = new Uint8Array(2);
      data2[0] = bits & 255;
      data2[1] = bits >> 8 & 255;
      return { data: data2, exc: NO_EXC };
    }
    if (rm !== RoundingMode.RNE) {
      return _encodeIeeeDirected(value, 5, 10, 15, rm);
    }
    if (Math.abs(value) >= _OVERFLOW_THRESH_F16) {
      const sign = value < 0 ? -1 : 1;
      const bits = sign < 0 ? 64512 : 31744;
      const data2 = new Uint8Array(2);
      data2[0] = bits & 255;
      data2[1] = bits >> 8 & 255;
      return { data: data2, exc: exc({ overflow: true, inexact: true }) };
    }
    const f16Bits = _encodeFloat16Rne(value);
    const data = new Uint8Array(2);
    data[0] = f16Bits & 255;
    data[1] = f16Bits >> 8 & 255;
    const rt = decodeFloat16Bits(f16Bits);
    const overflow = !Number.isFinite(rt) && Number.isFinite(value);
    const expBits = f16Bits >> 10 & 31;
    const isSub = expBits === 0 && (f16Bits & 1023) !== 0;
    const flushedToZero = rt === 0 && value !== 0;
    const exactSubnormal = 0 < Math.abs(value) && Math.abs(value) < _MIN_NORMAL_F16;
    const underflow = isSub || flushedToZero || exactSubnormal;
    const inexact = rt !== value;
    return {
      data,
      exc: exc({ overflow, underflow, inexact: inexact || overflow })
    };
  }
  function decodeFloat16Bits(bits) {
    const sign = bits >>> 15 & 1;
    const expField = bits >>> 10 & 31;
    const mant = bits & 1023;
    if (expField === 31) {
      if (mant !== 0) return NaN;
      return sign ? -Infinity : Infinity;
    }
    if (expField === 0) {
      if (mant === 0) return sign ? -0 : 0;
      const val2 = mant / 1024 * Math.pow(2, -14);
      return sign ? -val2 : val2;
    }
    const val = (1 + mant / 1024) * Math.pow(2, expField - 15);
    return sign ? -val : val;
  }
  function decodeFloat16(data) {
    const bits = data[0] | data[1] << 8;
    return decodeFloat16Bits(bits);
  }
  function _roundF32ToBf16(f32Bits) {
    let upper = f32Bits >>> 16 & 65535;
    const lower = f32Bits & 65535;
    const halfway = 32768;
    if (lower > halfway) {
      upper += 1;
    } else if (lower === halfway) {
      if (upper & 1) {
        upper += 1;
      }
    }
    return upper;
  }
  function encodeBfloat16(value, rm = 0) {
    if (Number.isNaN(value)) {
      const data2 = new Uint8Array(2);
      data2[0] = 192;
      data2[1] = 127;
      return { data: data2, exc: NO_EXC };
    }
    if (!Number.isFinite(value)) {
      const data2 = new Uint8Array(2);
      if (value > 0) {
        data2[0] = 128;
        data2[1] = 127;
      } else {
        data2[0] = 128;
        data2[1] = 255;
      }
      return { data: data2, exc: NO_EXC };
    }
    if (value === 0) {
      _f32arr[0] = value;
      const f32Bits2 = _u32arr[0];
      const upper2 = f32Bits2 >>> 16 & 65535;
      const data2 = new Uint8Array(2);
      data2[0] = upper2 & 255;
      data2[1] = upper2 >> 8 & 255;
      return { data: data2, exc: NO_EXC };
    }
    if (rm !== RoundingMode.RNE) {
      return _encodeIeeeDirected(value, 8, 7, 127, rm);
    }
    if (Math.abs(value) >= _OVERFLOW_THRESH_F32) {
      const bf16 = value < 0 ? 65408 : 32640;
      const data2 = new Uint8Array(2);
      data2[0] = bf16 & 255;
      data2[1] = bf16 >> 8 & 255;
      return { data: data2, exc: exc({ overflow: true, inexact: true }) };
    }
    _f32arr[0] = value;
    const f32Bits = _u32arr[0];
    const lower = f32Bits & 65535;
    const upper = _roundF32ToBf16(f32Bits);
    const data = new Uint8Array(2);
    data[0] = upper & 255;
    data[1] = upper >> 8 & 255;
    const rt = decodeBfloat16(data);
    const overflow = !Number.isFinite(rt) && Number.isFinite(value);
    const inexact = lower !== 0;
    const bfExp = upper >> 7 & 255;
    const bfMant = upper & 127;
    const flushed = rt === 0 && value !== 0;
    const underflow = bfExp === 0 && bfMant !== 0 || flushed;
    return {
      data,
      exc: exc({ overflow, underflow, inexact: inexact || overflow })
    };
  }
  function decodeBfloat16(data) {
    const upper = data[0] | data[1] << 8;
    _u32arr[0] = upper << 16;
    return _f32arr[0];
  }
  var _E4M3_BIAS = 7;
  var _E4M3_EXP_BITS = 4;
  var _E4M3_MANT_BITS = 3;
  var _E4M3_MAX_EXP = (1 << _E4M3_EXP_BITS) - 1;
  var _E4M3_MAX_FINITE = 448;
  function encodeOfp8E4M3(value, rm = 0) {
    if (Number.isNaN(value)) {
      return { data: new Uint8Array([127]), exc: exc({ invalid: true }) };
    }
    let sign = 0;
    if (value < 0 || value === 0 && Object.is(value, -0)) {
      sign = 1;
      value = -value;
    }
    if (!Number.isFinite(value)) {
      const byteVal2 = sign << 7 | 126;
      return { data: new Uint8Array([byteVal2]), exc: exc({ overflow: true, inexact: true }) };
    }
    if (value === 0) {
      return { data: new Uint8Array([sign << 7]), exc: NO_EXC };
    }
    if (value > _E4M3_MAX_FINITE) {
      const byteVal2 = sign << 7 | 126;
      return { data: new Uint8Array([byteVal2]), exc: exc({ overflow: true, inexact: true }) };
    }
    const { byteVal, exc: mExc } = _encodeMiniFloat(
      value,
      sign,
      _E4M3_EXP_BITS,
      _E4M3_MANT_BITS,
      _E4M3_BIAS,
      false,
      127,
      rm
    );
    return { data: new Uint8Array([byteVal]), exc: mExc };
  }
  function decodeOfp8E4M3(byteVal) {
    if (typeof byteVal !== "number") byteVal = byteVal[0];
    const sign = byteVal >> 7 & 1;
    const expField = byteVal >> _E4M3_MANT_BITS & _E4M3_MAX_EXP;
    const mant = byteVal & (1 << _E4M3_MANT_BITS) - 1;
    if (expField === _E4M3_MAX_EXP && mant === (1 << _E4M3_MANT_BITS) - 1) {
      return NaN;
    }
    if (expField === 0) {
      if (mant === 0) return sign ? -0 : 0;
      const val2 = mant / (1 << _E4M3_MANT_BITS) * Math.pow(2, 1 - _E4M3_BIAS);
      return sign ? -val2 : val2;
    }
    const val = (1 + mant / (1 << _E4M3_MANT_BITS)) * Math.pow(2, expField - _E4M3_BIAS);
    return sign ? -val : val;
  }
  var _E5M2_BIAS = 15;
  var _E5M2_EXP_BITS = 5;
  var _E5M2_MANT_BITS = 2;
  var _E5M2_MAX_EXP = (1 << _E5M2_EXP_BITS) - 1;
  function encodeOfp8E5M2(value, rm = 0) {
    if (Number.isNaN(value)) {
      return { data: new Uint8Array([125]), exc: exc({ invalid: true }) };
    }
    let sign = 0;
    if (value < 0 || value === 0 && Object.is(value, -0)) {
      sign = 1;
      value = -value;
    }
    if (!Number.isFinite(value)) {
      const byteVal2 = sign << 7 | _E5M2_MAX_EXP << _E5M2_MANT_BITS;
      return { data: new Uint8Array([byteVal2]), exc: NO_EXC };
    }
    if (value === 0) {
      return { data: new Uint8Array([sign << 7]), exc: NO_EXC };
    }
    const { byteVal, exc: mExc } = _encodeMiniFloat(
      value,
      sign,
      _E5M2_EXP_BITS,
      _E5M2_MANT_BITS,
      _E5M2_BIAS,
      true,
      null,
      rm
    );
    return { data: new Uint8Array([byteVal]), exc: mExc };
  }
  function decodeOfp8E5M2(byteVal) {
    if (typeof byteVal !== "number") byteVal = byteVal[0];
    const sign = byteVal >> 7 & 1;
    const expField = byteVal >> _E5M2_MANT_BITS & _E5M2_MAX_EXP;
    const mant = byteVal & (1 << _E5M2_MANT_BITS) - 1;
    if (expField === _E5M2_MAX_EXP) {
      if (mant === 0) return sign ? -Infinity : Infinity;
      return NaN;
    }
    if (expField === 0) {
      if (mant === 0) return sign ? -0 : 0;
      const val2 = mant / (1 << _E5M2_MANT_BITS) * Math.pow(2, 1 - _E5M2_BIAS);
      return sign ? -val2 : val2;
    }
    const val = (1 + mant / (1 << _E5M2_MANT_BITS)) * Math.pow(2, expField - _E5M2_BIAS);
    return sign ? -val : val;
  }
  function _overflowReturnsInf(rm, sign) {
    if (rm === RoundingMode.RTZ) return false;
    if (rm === RoundingMode.RDN) return sign === 1;
    if (rm === RoundingMode.RUP) return sign === 0;
    return true;
  }
  function _overflowResult(sign, expBits, mantBits, maxExp, maxNormalBiased, hasInf, nanPattern, rm) {
    if (hasInf && _overflowReturnsInf(rm, sign)) {
      const byteVal2 = sign << expBits + mantBits | maxExp << mantBits;
      return { byteVal: byteVal2, exc: exc({ overflow: true, inexact: true }) };
    }
    let maxMant = (1 << mantBits) - 1;
    if (nanPattern !== null) {
      maxMant -= 1;
    }
    const byteVal = sign << expBits + mantBits | maxNormalBiased << mantBits | maxMant;
    return { byteVal, exc: exc({ overflow: true, inexact: true }) };
  }
  function _encodeMiniFloat(absVal, sign, expBits, mantBits, bias, hasInf, nanPattern, rm) {
    const maxExp = (1 << expBits) - 1;
    const maxNormalBiased = hasInf ? maxExp - 1 : maxExp;
    const log2Val = Math.floor(Math.log2(absVal));
    let biasedExp = log2Val + bias;
    let mantInt;
    let underflow;
    if (biasedExp <= 0) {
      biasedExp = 0;
      const scale = Math.pow(2, 1 - bias);
      const mantFrac = absVal / scale;
      mantInt = _roundMantissa(mantFrac, mantBits, rm, sign, true);
      if (mantInt >= 1 << mantBits) {
        biasedExp = 1;
        mantInt -= 1 << mantBits;
      }
      underflow = true;
    } else if (biasedExp > maxNormalBiased) {
      return _overflowResult(
        sign,
        expBits,
        mantBits,
        maxExp,
        maxNormalBiased,
        hasInf,
        nanPattern,
        rm
      );
    } else {
      const significand = absVal / Math.pow(2, log2Val);
      const mantFrac = Math.max(0, significand - 1);
      mantInt = _roundMantissa(mantFrac, mantBits, rm, sign, false);
      if (mantInt >= 1 << mantBits) {
        mantInt = 0;
        biasedExp += 1;
        if (biasedExp > maxNormalBiased) {
          return _overflowResult(
            sign,
            expBits,
            mantBits,
            maxExp,
            maxNormalBiased,
            hasInf,
            nanPattern,
            rm
          );
        }
      }
      if (!hasInf && nanPattern !== null) {
        const candidate = biasedExp << mantBits | mantInt;
        if (candidate === (nanPattern & (1 << expBits + mantBits) - 1)) {
          mantInt -= 1;
        }
      }
      underflow = false;
    }
    const byteVal = sign << expBits + mantBits | biasedExp << mantBits | mantInt;
    let rtVal;
    if (biasedExp === 0) {
      rtVal = mantInt / (1 << mantBits) * Math.pow(2, 1 - bias);
    } else {
      rtVal = (1 + mantInt / (1 << mantBits)) * Math.pow(2, biasedExp - bias);
    }
    const inexact = rtVal !== absVal;
    return { byteVal, exc: exc({ underflow, inexact }) };
  }
  function _encodeIeeeDirected(value, expBits, mantBits, bias, rm) {
    let sign = 0;
    let absVal = value;
    if (value < 0) {
      sign = 1;
      absVal = -value;
    }
    const { byteVal: bits, exc: mExc } = _encodeMiniFloat(
      absVal,
      sign,
      expBits,
      mantBits,
      bias,
      true,
      null,
      rm
    );
    const width = 1 + expBits + mantBits;
    const numBytes = width >> 3;
    const data = new Uint8Array(numBytes);
    for (let i = 0; i < numBytes; i++) {
      data[i] = bits >> i * 8 & 255;
    }
    return { data, exc: mExc };
  }
  function _roundMantissa(frac, mantBits, rm, sign, _isDenorm) {
    const scale = 1 << mantBits;
    const scaled = frac * scale;
    const floorVal = Math.floor(scaled);
    const remainder = scaled - floorVal;
    if (remainder === 0) return floorVal;
    if (rm === RoundingMode.RNE) {
      if (remainder > 0.5) return floorVal + 1;
      if (remainder < 0.5) return floorVal;
      return floorVal & 1 ? floorVal + 1 : floorVal;
    }
    if (rm === RoundingMode.RTZ) {
      return floorVal;
    }
    if (rm === RoundingMode.RDN) {
      return sign ? floorVal + 1 : floorVal;
    }
    return sign ? floorVal : floorVal + 1;
  }
  function floatToBytes(value, fmt, rm = 0) {
    if (fmt === FP_FMT_F) return encodeFloat32(value, rm);
    if (fmt === FP_FMT_H) return encodeFloat16(value, rm);
    if (fmt === FP_FMT_BF) return encodeBfloat16(value, rm);
    if (fmt === FP_FMT_O3) return encodeOfp8E4M3(value, rm);
    if (fmt === FP_FMT_O2) return encodeOfp8E5M2(value, rm);
    throw new Error(`unsupported FP format code: ${fmt}`);
  }
  function bytesToFloat(data, fmt) {
    if (fmt === FP_FMT_F) return decodeFloat32(data);
    if (fmt === FP_FMT_H) return decodeFloat16(data);
    if (fmt === FP_FMT_BF) return decodeBfloat16(data);
    if (fmt === FP_FMT_O3) return decodeOfp8E4M3(data[0]);
    if (fmt === FP_FMT_O2) return decodeOfp8E5M2(data[0]);
    throw new Error(`unsupported FP format code: ${fmt}`);
  }
  function _reEncode(result, fmt, rm) {
    const { data, exc: encExc } = floatToBytes(result, fmt, rm);
    const rt = bytesToFloat(data, fmt);
    return { result: rt, exc: encExc };
  }
  function _addCore(a, b, fmt, rm) {
    let result = a + b;
    let absorbed = false;
    if (Number.isFinite(result)) {
      if (a !== 0 && result === b) {
        absorbed = true;
        result = nextafter(b, copysign(Infinity, a));
      } else if (b !== 0 && result === a) {
        absorbed = true;
        result = nextafter(a, copysign(Infinity, b));
      }
    }
    const { result: rt, exc: encExc } = _reEncode(result, fmt, rm);
    let finalExc = encExc;
    if (absorbed && !encExc.inexact) {
      finalExc = excReplace(encExc, { inexact: true });
    }
    return { result: rt, exc: finalExc };
  }
  function fpAdd(a, b, fmt, rm = 0) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (!Number.isFinite(a) && !Number.isFinite(b) && a !== b) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    return _addCore(a, b, fmt, rm);
  }
  function fpSub(a, b, fmt, rm = 0) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (!Number.isFinite(a) && !Number.isFinite(b) && a === b) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    return _addCore(a, -b, fmt, rm);
  }
  function fpMul(a, b, fmt, rm = 0) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (a === 0 && !Number.isFinite(b) || !Number.isFinite(a) && b === 0) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    const result = a * b;
    return _reEncode(result, fmt, rm);
  }
  function fpDiv(a, b, fmt, rm = 0) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (a === 0 && b === 0) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (!Number.isFinite(a) && !Number.isFinite(b)) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (b === 0) {
      const signA = copysign(1, a);
      const signB = copysign(1, b);
      const sign = signA * signB;
      return { result: copysign(Infinity, sign), exc: exc({ divZero: true }) };
    }
    const result = a / b;
    return _reEncode(result, fmt, rm);
  }
  function fpSqrt(value, fmt, rm = 0) {
    if (Number.isNaN(value)) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (value < 0) {
      return { result: NaN, exc: exc({ invalid: true }) };
    }
    if (value === 0) {
      return { result: copysign(0, value), exc: NO_EXC };
    }
    if (!Number.isFinite(value)) {
      return { result: Infinity, exc: NO_EXC };
    }
    const result = Math.sqrt(value);
    return _reEncode(result, fmt, rm);
  }
  function fpCmp(a, b) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
      return { zero: true, carry: true, exc: exc({ invalid: true }) };
    }
    if (a === b) {
      return { zero: true, carry: false, exc: NO_EXC };
    }
    if (a < b) {
      return { zero: false, carry: true, exc: NO_EXC };
    }
    return { zero: false, carry: false, exc: NO_EXC };
  }
  function fpAbs(rawBits, width) {
    const signMask = 1 << width - 1;
    return rawBits & ~signMask;
  }
  function fpNeg(rawBits, width) {
    const signMask = 1 << width - 1;
    return (rawBits ^ signMask) >>> 0;
  }
  var _FMT_SHAPE = {
    [FP_FMT_F]: [23, 8],
    [FP_FMT_H]: [10, 5],
    [FP_FMT_BF]: [7, 8],
    [FP_FMT_O3]: [3, 4],
    [FP_FMT_O2]: [2, 5]
  };
  function _isSubnormal(rawBits, width, fmt) {
    const shape = _FMT_SHAPE[fmt];
    if (!shape) return false;
    const [mantBits, expBits] = shape;
    const expField = rawBits >> mantBits & (1 << expBits) - 1;
    const mant = rawBits & (1 << mantBits) - 1;
    return expField === 0 && mant !== 0;
  }
  function fpClassify(value, rawBits, width, fmt) {
    let result = 0;
    const signMask = 1 << width - 1;
    if (rawBits & signMask) {
      result |= 64;
    }
    if (Number.isNaN(value)) {
      result |= 16;
      return result;
    }
    if (!Number.isFinite(value)) {
      result |= 8;
      return result;
    }
    if (value === 0) {
      result |= 1;
      return result;
    }
    if (_isSubnormal(rawBits, width, fmt)) {
      result |= 2;
    } else {
      result |= 4;
    }
    return result;
  }

  // asm.js
  var AsmError = class extends Error {
    constructor(message, line) {
      super(`Line ${line}: ${message}`);
      this.message = message;
      this.line = line;
    }
  };
  var ALL_MNEMONICS_V2 = /* @__PURE__ */ new Set([...MNEMONICS, ...MNEMONICS_FP]);
  var TAG_REG = "reg";
  var TAG_CONST = "const";
  var TAG_ADDR = "addr";
  var TAG_REGADDR = "regaddr";
  var TAG_STRING = "string";
  var TAG_LABEL = "label";
  var TAG_ADDR_LABEL = "addr_label";
  var TAG_FP_REG = "fp_reg";
  var TAG_FLOAT = "float";
  var TAG_FP_IMM = "fp_imm";
  var _RE_HEX = /^0x([0-9A-Fa-f]+)$/;
  var _RE_OCT = /^0o([0-7]+)$/;
  var _RE_BIN = /^([01]+)b$/;
  var _RE_DEC_EXPLICIT = /^(\d+)d$/;
  var _RE_DEC = /^(\d+)$/;
  var _RE_CHAR = /^'(.)'$/;
  var _RE_CHAR_MULTI = /^'(.{2,})'$/;
  var _NUM_FORMATS = [
    [_RE_HEX, 16],
    [_RE_OCT, 8],
    [_RE_BIN, 2],
    [_RE_DEC_EXPLICIT, 10],
    [_RE_DEC, 10]
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
  var _RE_LABEL = /^[.A-Za-z]\w*$/;
  var _RE_FLOAT = /^([+-]?)(\d+\.\d*|\.\d+)([eE][+-]?\d+)?(_\w+)?$/;
  var _RE_FLOAT_SPECIAL = /^([+-]?)(inf|nan)(_\w+)?$/i;
  var _RE_BRACKET = /^\[(.+)\]$/;
  var _RE_REG_OFFSET = /^([A-Za-z]+)\s*([+-])\s*(\d+)$/;
  var _RE_REG_ONLY = /^([A-Za-z]+)$/;
  function _parseBracketOperand(inner, line) {
    inner = inner.trim();
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
    m = _RE_REG_ONLY.exec(inner);
    if (m) {
      const regName = m[1].toUpperCase();
      if (regName in REGISTERS) {
        return { tag: TAG_REGADDR, regCode: REGISTERS[regName], offset: 0 };
      }
    }
    const val = _tryParseNumber(inner);
    if (val !== null) {
      _checkByteRange(val, line);
      return { tag: TAG_ADDR, value: val };
    }
    if (_RE_LABEL.test(inner)) {
      return { tag: TAG_ADDR_LABEL, name: inner.toLowerCase() };
    }
    throw new AsmError(`Invalid address: ${inner}`, line);
  }
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
  function _resolveFpImmSuffix(suffixStr, line) {
    if (suffixStr == null) return null;
    const suffix = suffixStr.slice(1).toUpperCase();
    if (!(suffix in FP_DB_SUFFIX_TO_FMT)) {
      throw new AsmError("Invalid float literal", line);
    }
    return FP_DB_SUFFIX_TO_FMT[suffix];
  }
  function _tryFpImm(token, line) {
    let m = _RE_FLOAT_SPECIAL.exec(token);
    if (m) {
      const signStr = m[1];
      const name = m[2];
      const suffixStr = m[3] || null;
      const fmt = _resolveFpImmSuffix(suffixStr, line);
      let val;
      if (name.toLowerCase() === "inf") {
        val = signStr === "-" ? -Infinity : Infinity;
      } else {
        val = NaN;
        if (signStr === "-") val = -val;
      }
      return { tag: TAG_FP_IMM, value: val, fmt };
    }
    m = _RE_FLOAT.exec(token);
    if (m) {
      const signStr = m[1];
      const num = m[2];
      const exp = m[3] || "";
      const suffixStr = m[4] || null;
      const fmt = _resolveFpImmSuffix(suffixStr, line);
      const text = (signStr || "") + num + exp;
      const val = parseFloat(text);
      if (Number.isNaN(val) && text.toLowerCase() !== "nan") {
        throw new AsmError("Invalid float literal", line);
      }
      return { tag: TAG_FP_IMM, value: val, fmt };
    }
    return null;
  }
  function _tryLabel(token, _line) {
    if (_RE_LABEL.test(token)) {
      return { tag: TAG_LABEL, name: token.toLowerCase() };
    }
    return null;
  }
  var _OPERAND_PARSERS = [
    _tryBracket,
    _tryRegister,
    _tryString,
    _tryConst,
    _tryFpImm,
    _tryLabel
  ];
  function _parseOperand(token, line) {
    token = token.trim();
    for (const parser of _OPERAND_PARSERS) {
      const result = parser(token, line);
      if (result !== null) return result;
    }
    throw new AsmError(`Invalid operand: ${token}`, line);
  }
  function _resolveDbFloatSuffix(suffixStr, line) {
    if (suffixStr == null) return FP_FMT_F;
    const suffix = suffixStr.slice(1).toUpperCase();
    if (!(suffix in FP_DB_SUFFIX_TO_FMT)) {
      throw new AsmError("Invalid float literal", line);
    }
    const fmt = FP_DB_SUFFIX_TO_FMT[suffix];
    if (fmt === FP_FMT_N1 || fmt === FP_FMT_N2) {
      throw new AsmError(
        `Unsupported float format for DB: ${suffixStr.slice(1)}`,
        line
      );
    }
    return fmt;
  }
  function _parseFloatLiteral(token, line) {
    let m = _RE_FLOAT_SPECIAL.exec(token);
    if (m) {
      const signStr = m[1];
      const name = m[2];
      const suffixStr = m[3] || null;
      const fmt = _resolveDbFloatSuffix(suffixStr, line);
      let val;
      if (name.toLowerCase() === "inf") {
        val = signStr === "-" ? -Infinity : Infinity;
      } else {
        val = NaN;
        if (signStr === "-") val = -val;
      }
      return { tag: TAG_FLOAT, value: val, fmt };
    }
    m = _RE_FLOAT.exec(token);
    if (m) {
      const signStr = m[1];
      const num = m[2];
      const exp = m[3] || "";
      const suffixStr = m[4] || null;
      const fmt = _resolveDbFloatSuffix(suffixStr, line);
      const text = (signStr || "") + num + exp;
      const val = parseFloat(text);
      if (Number.isNaN(val) && text.toLowerCase() !== "nan") {
        throw new AsmError("Invalid float literal", line);
      }
      return { tag: TAG_FLOAT, value: val, fmt };
    }
    return null;
  }
  function _parseDbOperands(raw, line, arch) {
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
      if (up in REGISTERS) {
        throw new AsmError("DB does not support this operand", line);
      }
      if (arch >= 2) {
        const fp = _parseFloatLiteral(part, line);
        if (fp !== null) {
          if (hasInt) {
            throw new AsmError(
              "DB does not support mixing float and integer operands",
              line
            );
          }
          hasFloat = true;
          operands.push(fp);
          continue;
        }
      }
      if (hasFloat) {
        throw new AsmError(
          "DB does not support mixing float and integer operands",
          line
        );
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
  var _RE_LABEL_DEF = /^([.A-Za-z]\w*)\s*:/;
  function _parseLine(raw, lineNo, arch) {
    const text = _tokenizeLine(raw);
    const result = {
      lineNo,
      label: null,
      mnemonic: null,
      operands: null,
      dstSuffix: null,
      srcSuffix: null
    };
    if (!text) return result;
    let remaining = text;
    const labelMatch = _RE_LABEL_DEF.exec(remaining);
    if (labelMatch) {
      const labelName = labelMatch[1];
      if (labelName.toUpperCase() in REGISTERS) {
        throw new AsmError(
          `Label contains keyword: ${labelName.toUpperCase()}`,
          lineNo
        );
      }
      if (arch >= 2 && labelName.toUpperCase() in FP_REGISTERS) {
        throw new AsmError(
          `Label contains keyword: ${labelName.toUpperCase()}`,
          lineNo
        );
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
    if (operandStr) {
      const tokens = _splitOperands(operandStr);
      result.operands = tokens.map((t) => _parseOperand(t, lineNo));
    } else {
      result.operands = [];
    }
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
        return 0;
      // placeholder for pass 2
      case TAG_ADDR_LABEL:
        return 0;
      // placeholder for pass 2
      default:
        throw new Error(`unexpected operand: ${op.tag}`);
    }
  }
  function _findInsn(mnemonic, operands, line, table) {
    if (table == null) table = BY_MNEMONIC;
    const candidates = table[mnemonic];
    if (!candidates) {
      throw new AsmError(`Invalid instruction: ${mnemonic}`, line);
    }
    for (const insn2 of candidates) {
      if (insn2.sig.length !== operands.length) continue;
      let allMatch = true;
      for (let i = 0; i < insn2.sig.length; i++) {
        if (!_operandMatches(operands[i], insn2.sig[i])) {
          allMatch = false;
          break;
        }
      }
      if (allMatch) return insn2;
    }
    let maxArity = 0;
    for (const insn2 of candidates) {
      if (insn2.sig.length > maxArity) maxArity = insn2.sig.length;
    }
    if (operands.length > maxArity) {
      throw new AsmError(`${mnemonic}: too many arguments`, line);
    }
    throw new AsmError(`${mnemonic} does not support this operand(s)`, line);
  }
  function _encodeDbOperand(op, line, result) {
    if (op.tag === TAG_CONST) {
      result.push(op.value);
      return;
    }
    if (op.tag === TAG_STRING) {
      if (!op.text) {
        throw new AsmError("DB string must not be empty", line);
      }
      for (let i = 0; i < op.text.length; i++) {
        result.push(op.text.charCodeAt(i));
      }
      return;
    }
    if (op.tag === TAG_FLOAT) {
      const { data } = floatToBytes(op.value, op.fmt);
      for (let i = 0; i < data.length; i++) {
        result.push(data[i]);
      }
      return;
    }
    throw new AsmError(`DB does not support this operand`, line);
  }
  function _encodeDb(operands, line) {
    const result = [];
    for (const op of operands) {
      _encodeDbOperand(op, line, result);
    }
    return result;
  }
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
      throw new AsmError(
        "FP format suffix does not match register width",
        line
      );
    }
  }
  function _encodeFpInstruction(insn2, operands, dstSuffix, srcSuffix, line) {
    const dstFmt = dstSuffix ? _validateFpSuffix(dstSuffix, line) : null;
    const srcFmt = srcSuffix ? _validateFpSuffix(srcSuffix, line) : null;
    if (insn2.op === Op.FCVT_FP_FP) {
      if (dstFmt === srcFmt) {
        throw new AsmError("FCVT with identical formats (use FMOV)", line);
      }
      const dstReg = operands[0];
      const srcReg = operands[1];
      _validateFpRegWidth(dstReg, dstFmt, line);
      _validateFpRegWidth(srcReg, srcFmt, line);
      const dstFpm = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);
      const srcFpm = encodeFpm(srcReg.phys, srcReg.pos, srcFmt);
      return [insn2.op, dstFpm, srcFpm];
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
    return [insn2.op, ...fpmBytes, ...nonFpBytes];
  }
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
    if (fpImm.fmt !== null && fpImm.fmt !== dstFmt) {
      throw new AsmError("FP immediate suffix mismatch", line);
    }
    _validateFpRegWidth(dstReg, dstFmt, line);
    const { data } = floatToBytes(fpImm.value, dstFmt);
    const fpmByte = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);
    if (fmtWidth === 8) {
      return [Op.FMOV_FP_IMM8, fpmByte, data[0]];
    }
    return [Op.FMOV_FP_IMM16, fpmByte, data[0], data[1]];
  }
  function _encodeInstruction(mnemonic, operands, line, dstSuffix, srcSuffix, arch) {
    if (mnemonic === "DB") {
      return _encodeDb(operands, line);
    }
    if (arch >= 2 && MNEMONICS_FP.has(mnemonic)) {
      if (mnemonic === "FMOV" && operands.length === 2 && operands[1].tag === TAG_FP_IMM) {
        return _encodeFmovImm(operands, dstSuffix, line);
      }
      const insn3 = _findInsn(mnemonic, operands, line, BY_MNEMONIC_FP);
      if (FP_CONTROL_MNEMONICS.has(mnemonic)) {
        return [insn3.op, ...operands.map((op) => _encodeOperand(op))];
      }
      return _encodeFpInstruction(insn3, operands, dstSuffix, srcSuffix, line);
    }
    const insn2 = _findInsn(mnemonic, operands, line, BY_MNEMONIC);
    return [insn2.op, ...operands.map((op) => _encodeOperand(op))];
  }
  function assemble(source, arch = 2) {
    const parsed = _parseLines(source, arch);
    const code = [];
    const labels = {};
    const mapping = {};
    const labelPatches = [];
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
        arch
      );
      if (pline.mnemonic !== "DB") {
        mapping[pos] = pline.lineNo;
      }
      if (operands.length > 0) {
        for (let i = 0; i < operands.length; i++) {
          const op = operands[i];
          if (op.tag === TAG_LABEL || op.tag === TAG_ADDR_LABEL) {
            const isFpData = arch >= 2 && MNEMONICS_FP.has(pline.mnemonic) && !FP_CONTROL_MNEMONICS.has(pline.mnemonic);
            if (isFpData) {
              let fpCount = 0;
              for (const o of operands) {
                if (o.tag === TAG_FP_REG) fpCount++;
              }
              let nonFpIdx = 0;
              for (let j = 0; j < i; j++) {
                if (operands[j].tag !== TAG_FP_REG) nonFpIdx++;
              }
              labelPatches.push([pos + 1 + fpCount + nonFpIdx, op.name, pline.lineNo]);
            } else {
              labelPatches.push([pos + 1 + i, op.name, pline.lineNo]);
            }
          }
        }
      }
      for (const byte of encoded) {
        code.push(byte);
      }
    }
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
    return { code, labels, mapping };
  }

  // core.js
  var MEMORY_SIZE = 65536;
  var PAGE_SIZE = 256;
  var IO_START = 232;
  var SP_INIT = 231;
  var CpuState = Object.freeze({
    IDLE: "IDLE",
    RUNNING: "RUNNING",
    HALTED: "HALTED",
    FAULT: "FAULT"
  });
  var ErrorCode = Object.freeze({
    DIV_ZERO: 1,
    STACK_OVERFLOW: 2,
    STACK_UNDERFLOW: 3,
    INVALID_REG: 4,
    PAGE_BOUNDARY: 5,
    INVALID_OPCODE: 6,
    FP_FORMAT: 12
  });
  var CpuFault = class extends Error {
    constructor(code, ip = 0) {
      super(`FAULT(${code}) at IP=${ip}`);
      this.code = code;
      this.ip = ip;
    }
  };
  var Memory = class {
    constructor() {
      this._data = new Uint8Array(MEMORY_SIZE);
    }
    get(addr) {
      return this._data[addr];
    }
    set(addr, val) {
      this._data[addr] = val & 255;
    }
    load(data, offset = 0) {
      if (offset + data.length > MEMORY_SIZE) {
        throw new RangeError(
          `Data (${data.length} bytes at offset ${offset}) exceeds memory size (${MEMORY_SIZE})`
        );
      }
      for (let i = 0; i < data.length; i++) {
        this._data[offset + i] = data[i] & 255;
      }
    }
    reset() {
      this._data.fill(0);
    }
  };
  var ALU = {
    add(a, b) {
      const raw = a + b;
      const carry = raw > 255;
      const result = raw & 255;
      return [result, carry, result === 0];
    },
    sub(a, b) {
      const raw = a - b;
      const carry = raw < 0;
      const result = (raw % 256 + 256) % 256;
      return [result, carry, result === 0];
    },
    mul(a, b) {
      const raw = a * b;
      const carry = raw > 255;
      const result = raw & 255;
      return [result, carry, result === 0];
    },
    div(a, b) {
      const result = Math.floor(a / b);
      const carry = result > 255 || result < 0;
      const clamped = (result % 256 + 256) % 256;
      return [clamped, carry, clamped === 0];
    },
    inc(a) {
      const raw = a + 1;
      const carry = raw > 255;
      const result = raw & 255;
      return [result, carry, result === 0];
    },
    dec(a) {
      const raw = a - 1;
      const carry = raw < 0;
      const result = (raw % 256 + 256) % 256;
      return [result, carry, result === 0];
    },
    and_op(a, b) {
      const result = a & b;
      return [result, result === 0];
    },
    or_op(a, b) {
      const result = a | b;
      return [result, result === 0];
    },
    xor_op(a, b) {
      const result = a ^ b;
      return [result, result === 0];
    },
    not_op(a) {
      const result = a ^ 255;
      return [result, result === 0];
    },
    shl(value, count) {
      const raw = value * (1 << count);
      const carry = raw > 255;
      const result = raw & 255;
      return [result, carry, result === 0];
    },
    shr(value, count) {
      const carry = value % (1 << count) !== 0;
      const result = value >> count;
      return [result, carry, result === 0];
    }
  };
  var Flags = class {
    constructor() {
      this.z = false;
      this.c = false;
      this.f = false;
    }
    reset() {
      this.z = false;
      this.c = false;
      this.f = false;
    }
  };
  var _fpBuf = new ArrayBuffer(4);
  var _fpF32 = new Float32Array(_fpBuf);
  var _fpU32 = new Uint32Array(_fpBuf);
  var FpuRegisters = class {
    constructor() {
      this._fp32 = [0, 0];
      this.fpcr = 0;
      this.fpsr = 0;
    }
    get fa() {
      _fpU32[0] = this._fp32[0] >>> 0;
      return _fpF32[0];
    }
    get fb() {
      _fpU32[0] = this._fp32[1] >>> 0;
      return _fpF32[0];
    }
    get roundingMode() {
      return this.fpcr & 3;
    }
    readBits(pos, fmt, phys = 0) {
      const width = FP_FMT_WIDTH[fmt];
      if (width === 32) {
        return this._fp32[phys] >>> 0;
      }
      const bitOffset = pos * width;
      const mask = (1 << width) - 1;
      return this._fp32[phys] >> bitOffset & mask;
    }
    writeBits(pos, fmt, value, phys = 0) {
      const width = FP_FMT_WIDTH[fmt];
      if (width === 32) {
        this._fp32[phys] = value >>> 0;
        return;
      }
      const bitOffset = pos * width;
      const mask = (1 << width) - 1;
      this._fp32[phys] = (this._fp32[phys] & ~(mask << bitOffset) | (value & mask) << bitOffset) >>> 0;
    }
    accumulateExceptions(exc2) {
      if (exc2.invalid) this.fpsr |= 1;
      if (exc2.divZero) this.fpsr |= 2;
      if (exc2.overflow) this.fpsr |= 4;
      if (exc2.underflow) this.fpsr |= 8;
      if (exc2.inexact) this.fpsr |= 16;
    }
    reset() {
      this._fp32[0] = 0;
      this._fp32[1] = 0;
      this.fpcr = 0;
      this.fpsr = 0;
    }
  };
  var RegisterFile = class {
    constructor(arch = 1) {
      this._regs = [0, 0, 0, 0, SP_INIT, 0];
      this.ip = 0;
      this.flags = new Flags();
      this.fpu = arch >= 2 ? new FpuRegisters() : null;
    }
    read(code) {
      return this._regs[code];
    }
    write(code, val) {
      this._regs[code] = val & 255;
    }
    get a() {
      return this._regs[0];
    }
    set a(val) {
      this._regs[0] = val & 255;
    }
    get b() {
      return this._regs[1];
    }
    set b(val) {
      this._regs[1] = val & 255;
    }
    get c() {
      return this._regs[2];
    }
    set c(val) {
      this._regs[2] = val & 255;
    }
    get d() {
      return this._regs[3];
    }
    set d(val) {
      this._regs[3] = val & 255;
    }
    get sp() {
      return this._regs[4];
    }
    set sp(val) {
      this._regs[4] = val & 255;
    }
    get dp() {
      return this._regs[5];
    }
    set dp(val) {
      this._regs[5] = val & 255;
    }
    reset(arch = 1) {
      this._regs = [0, 0, 0, 0, SP_INIT, 0];
      this.ip = 0;
      this.flags.reset();
      if (arch >= 2) {
        if (this.fpu === null) {
          this.fpu = new FpuRegisters();
        } else {
          this.fpu.reset();
        }
      } else {
        this.fpu = null;
      }
    }
  };
  function decode(mem, ip, arch) {
    const opcode = mem.get(ip);
    let defn = BY_CODE[opcode];
    if (defn === void 0 && arch >= 2) {
      defn = BY_CODE_FP[opcode];
    }
    if (defn === void 0) {
      throw new CpuFault(ErrorCode.INVALID_OPCODE, ip);
    }
    const size = defn.size;
    if (ip + size > PAGE_SIZE) {
      throw new CpuFault(ErrorCode.PAGE_BOUNDARY, ip);
    }
    const operands = [];
    for (let k = 1; k < size; k++) {
      operands.push(mem.get(ip + k));
    }
    return { op: defn.op, size, operands };
  }
  function intFromBytesLE(data) {
    let raw = 0;
    for (let i = data.length - 1; i >= 0; i--) {
      raw = raw << 8 | data[i];
    }
    if (data.length === 4) return raw >>> 0;
    return raw;
  }
  function intToBytesLE(raw, nbytes) {
    const data = new Uint8Array(nbytes);
    for (let i = 0; i < nbytes; i++) {
      data[i] = raw >> i * 8 & 255;
    }
    return data;
  }
  var CPU = class {
    constructor({ arch = 2 } = {}) {
      this.mem = new Memory();
      this.regs = new RegisterFile(arch);
      this.state = CpuState.IDLE;
      this._steps = 0;
      this._cycles = 0;
      this._arch = arch;
      this._dispatch = {};
      this._buildDispatch();
      if (arch >= 2) {
        this._buildFpDispatch();
      }
      const allIsa = arch < 2 ? ISA : ISA.concat(ISA_FP);
      this._opCost = {};
      for (const d of allIsa) {
        this._opCost[d.op] = d.cost;
      }
    }
    // ── Public API ───────────────────────────────────────────────
    load(code) {
      this.reset();
      this.mem.load(code);
    }
    step() {
      if (this.state === CpuState.FAULT || this.state === CpuState.HALTED) {
        return false;
      }
      if (this.state === CpuState.IDLE) {
        this.state = CpuState.RUNNING;
      }
      let insn2;
      try {
        insn2 = decode(this.mem, this.regs.ip, this._arch);
      } catch (e) {
        if (e instanceof CpuFault) {
          this._enterFault(e.code);
          return false;
        }
        throw e;
      }
      if (insn2.op === Op.HLT) {
        this.state = CpuState.HALTED;
        return false;
      }
      try {
        const handler = this._dispatch[insn2.op];
        handler(insn2);
      } catch (e) {
        if (e instanceof CpuFault) {
          this._enterFault(e.code);
          return false;
        }
        throw e;
      }
      this._steps += 1;
      this._cycles += this._opCost[insn2.op] || 1;
      return this.state === CpuState.RUNNING;
    }
    run(maxSteps = 1e5) {
      for (let i = 0; i < maxSteps; i++) {
        if (!this.step()) break;
      }
      return this.state;
    }
    reset() {
      this.mem.reset();
      this.regs.reset(this._arch);
      this.state = CpuState.IDLE;
      this._steps = 0;
      this._cycles = 0;
    }
    get steps() {
      return this._steps;
    }
    get cycles() {
      return this._cycles;
    }
    get a() {
      return this.regs.a;
    }
    get b() {
      return this.regs.b;
    }
    get c() {
      return this.regs.c;
    }
    get d() {
      return this.regs.d;
    }
    get sp() {
      return this.regs.sp;
    }
    get dp() {
      return this.regs.dp;
    }
    get ip() {
      return this.regs.ip;
    }
    get zero() {
      return this.regs.flags.z;
    }
    get carry() {
      return this.regs.flags.c;
    }
    get fault() {
      return this.regs.flags.f;
    }
    get fpu() {
      return this.regs.fpu;
    }
    display() {
      const chars = [];
      for (let addr = IO_START; addr < PAGE_SIZE; addr++) {
        const b = this.mem.get(addr);
        chars.push(b >= 33 && b <= 126 ? String.fromCharCode(b) : " ");
      }
      return chars.join("").trimEnd();
    }
    // ── Fault handling ─────────────────────────────────────────────
    _enterFault(code) {
      this.regs.flags.f = true;
      this.regs.a = code;
      this.state = CpuState.FAULT;
    }
    // ── Address resolution ─────────────────────────────────────────
    _directAddr(offset) {
      return this.regs.dp * PAGE_SIZE + offset;
    }
    _indirectAddr(encoded) {
      const [reg, offset] = decodeRegaddr(encoded);
      if (reg > Reg.SP) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
      }
      const base = reg === Reg.SP ? this.regs.sp : this.regs.read(reg);
      const pageOffset = base + offset;
      if (pageOffset < 0 || pageOffset >= PAGE_SIZE) {
        throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
      }
      if (reg === Reg.SP) return pageOffset;
      return this.regs.dp * PAGE_SIZE + pageOffset;
    }
    // ── Register validation ────────────────────────────────────────
    _decodeGpr(code) {
      if (code > 3) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
      }
      return code;
    }
    _decodeGprOrSp(code) {
      if (code > Reg.SP) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
      }
      return code;
    }
    _decodeMovReg(code) {
      if (code > Reg.DP) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
      }
      return code;
    }
    // ── Source resolvers ───────────────────────────────────────────
    _srcRegaddr(insn2) {
      return this.mem.get(this._indirectAddr(insn2.operands[1]));
    }
    _srcAddr(insn2) {
      return this.mem.get(this._directAddr(insn2.operands[1]));
    }
    _srcConst(insn2) {
      return insn2.operands[1];
    }
    _srcStkReg(insn2) {
      const code = this._decodeGprOrSp(insn2.operands[1]);
      return this.regs.read(code);
    }
    _srcGprReg(insn2) {
      const code = this._decodeGpr(insn2.operands[1]);
      return this.regs.read(code);
    }
    _srcMuldivReg(insn2) {
      const code = this._decodeGpr(insn2.operands[0]);
      return this.regs.read(code);
    }
    _srcMuldivRegaddr(insn2) {
      return this.mem.get(this._indirectAddr(insn2.operands[0]));
    }
    _srcMuldivAddr(insn2) {
      return this.mem.get(this._directAddr(insn2.operands[0]));
    }
    _srcMuldivConst(insn2) {
      return insn2.operands[0];
    }
    // ── Stack helpers ──────────────────────────────────────────────
    _doPush(value) {
      if (this.regs.sp === 0) {
        throw new CpuFault(ErrorCode.STACK_OVERFLOW, this.regs.ip);
      }
      this.mem.set(this.regs.sp, value);
      this.regs.sp = this.regs.sp - 1;
    }
    _doPop() {
      if (this.regs.sp >= SP_INIT) {
        throw new CpuFault(ErrorCode.STACK_UNDERFLOW, this.regs.ip);
      }
      this.regs.sp = this.regs.sp + 1;
      return this.mem.get(this.regs.sp);
    }
    // ── Handler factories ──────────────────────────────────────────
    _makeAlu2op(aluFn, resolveSrc, writeback = true) {
      return (insn2) => {
        const destCode = this._decodeGprOrSp(insn2.operands[0]);
        const right = resolveSrc(insn2);
        const left = this.regs.read(destCode);
        const [result, carry, zero] = aluFn(left, right);
        this.regs.flags.c = carry;
        this.regs.flags.z = zero;
        if (writeback) {
          this.regs.write(destCode, result);
        }
        this.regs.ip += insn2.size;
      };
    }
    _makeBitwise2op(aluFn, resolveSrc) {
      return (insn2) => {
        const destCode = this._decodeGpr(insn2.operands[0]);
        const right = resolveSrc(insn2);
        const left = this.regs.read(destCode);
        const [result, zero] = aluFn(left, right);
        this.regs.flags.c = false;
        this.regs.flags.z = zero;
        this.regs.write(destCode, result);
        this.regs.ip += insn2.size;
      };
    }
    _makeShift2op(aluFn, resolveSrc) {
      return (insn2) => {
        const destCode = this._decodeGpr(insn2.operands[0]);
        const count = resolveSrc(insn2);
        const value = this.regs.read(destCode);
        if (count === 0) {
          this.regs.flags.z = value === 0;
        } else {
          const [result, carry, zero] = aluFn(value, count);
          this.regs.flags.c = carry;
          this.regs.flags.z = zero;
          this.regs.write(destCode, result);
        }
        this.regs.ip += insn2.size;
      };
    }
    _makeJcc(condition, isReg) {
      return (insn2) => {
        let target;
        if (isReg) {
          const code = this._decodeGpr(insn2.operands[0]);
          target = this.regs.read(code);
        } else {
          target = insn2.operands[0];
        }
        if (condition()) {
          this.regs.ip = target;
        } else {
          this.regs.ip += insn2.size;
        }
      };
    }
    _makeMuldiv(aluFn, resolveSrc) {
      return (insn2) => {
        const right = resolveSrc(insn2);
        const [result, carry, zero] = aluFn(this.regs.a, right);
        this.regs.flags.c = carry;
        this.regs.flags.z = zero;
        this.regs.a = result;
        this.regs.ip += insn2.size;
      };
    }
    _makeDiv(resolveSrc) {
      return (insn2) => {
        const right = resolveSrc(insn2);
        if (right === 0) {
          throw new CpuFault(ErrorCode.DIV_ZERO, this.regs.ip);
        }
        const [result, carry, zero] = ALU.div(this.regs.a, right);
        this.regs.flags.c = carry;
        this.regs.flags.z = zero;
        this.regs.a = result;
        this.regs.ip += insn2.size;
      };
    }
    // ── Integer dispatch table ─────────────────────────────────────
    _buildDispatch() {
      const d = this._dispatch;
      d[Op.MOV_REG_REG] = (insn2) => {
        const dest = this._decodeMovReg(insn2.operands[0]);
        const src = this._decodeMovReg(insn2.operands[1]);
        this.regs.write(dest, this.regs.read(src));
        this.regs.ip += insn2.size;
      };
      d[Op.MOV_REG_ADDR] = (insn2) => {
        const dest = this._decodeMovReg(insn2.operands[0]);
        this.regs.write(dest, this.mem.get(this._directAddr(insn2.operands[1])));
        this.regs.ip += insn2.size;
      };
      d[Op.MOV_REG_REGADDR] = (insn2) => {
        const dest = this._decodeMovReg(insn2.operands[0]);
        this.regs.write(dest, this.mem.get(this._indirectAddr(insn2.operands[1])));
        this.regs.ip += insn2.size;
      };
      d[Op.MOV_ADDR_REG] = (insn2) => {
        const addr = this._directAddr(insn2.operands[0]);
        const src = this._decodeMovReg(insn2.operands[1]);
        this.mem.set(addr, this.regs.read(src));
        this.regs.ip += insn2.size;
      };
      d[Op.MOV_REGADDR_REG] = (insn2) => {
        const addr = this._indirectAddr(insn2.operands[0]);
        const src = this._decodeMovReg(insn2.operands[1]);
        this.mem.set(addr, this.regs.read(src));
        this.regs.ip += insn2.size;
      };
      d[Op.MOV_REG_CONST] = (insn2) => {
        const dest = this._decodeMovReg(insn2.operands[0]);
        this.regs.write(dest, insn2.operands[1]);
        this.regs.ip += insn2.size;
      };
      d[Op.MOV_ADDR_CONST] = (insn2) => {
        const addr = this._directAddr(insn2.operands[0]);
        this.mem.set(addr, insn2.operands[1]);
        this.regs.ip += insn2.size;
      };
      d[Op.MOV_REGADDR_CONST] = (insn2) => {
        const addr = this._indirectAddr(insn2.operands[0]);
        this.mem.set(addr, insn2.operands[1]);
        this.regs.ip += insn2.size;
      };
      const srcStk = (i) => this._srcStkReg(i);
      const srcRA = (i) => this._srcRegaddr(i);
      const srcA = (i) => this._srcAddr(i);
      const srcC = (i) => this._srcConst(i);
      for (const [base, aluFn] of [[Op.ADD_REG_REG, ALU.add], [Op.SUB_REG_REG, ALU.sub]]) {
        d[base + 0] = this._makeAlu2op(aluFn, srcStk);
        d[base + 1] = this._makeAlu2op(aluFn, srcRA);
        d[base + 2] = this._makeAlu2op(aluFn, srcA);
        d[base + 3] = this._makeAlu2op(aluFn, srcC);
      }
      d[Op.INC_REG] = (insn2) => {
        const code = this._decodeGprOrSp(insn2.operands[0]);
        const [result, carry, zero] = ALU.inc(this.regs.read(code));
        this.regs.flags.c = carry;
        this.regs.flags.z = zero;
        this.regs.write(code, result);
        this.regs.ip += insn2.size;
      };
      d[Op.DEC_REG] = (insn2) => {
        const code = this._decodeGprOrSp(insn2.operands[0]);
        const [result, carry, zero] = ALU.dec(this.regs.read(code));
        this.regs.flags.c = carry;
        this.regs.flags.z = zero;
        this.regs.write(code, result);
        this.regs.ip += insn2.size;
      };
      d[Op.CMP_REG_REG] = this._makeAlu2op(ALU.sub, srcStk, false);
      d[Op.CMP_REG_REGADDR] = this._makeAlu2op(ALU.sub, srcRA, false);
      d[Op.CMP_REG_ADDR] = this._makeAlu2op(ALU.sub, srcA, false);
      d[Op.CMP_REG_CONST] = this._makeAlu2op(ALU.sub, srcC, false);
      d[Op.JMP_REG] = (insn2) => {
        const code = this._decodeGpr(insn2.operands[0]);
        this.regs.ip = this.regs.read(code);
      };
      d[Op.JMP_ADDR] = (insn2) => {
        this.regs.ip = insn2.operands[0];
      };
      d[Op.JC_REG] = this._makeJcc(() => this.regs.flags.c, true);
      d[Op.JC_ADDR] = this._makeJcc(() => this.regs.flags.c, false);
      d[Op.JNC_REG] = this._makeJcc(() => !this.regs.flags.c, true);
      d[Op.JNC_ADDR] = this._makeJcc(() => !this.regs.flags.c, false);
      d[Op.JZ_REG] = this._makeJcc(() => this.regs.flags.z, true);
      d[Op.JZ_ADDR] = this._makeJcc(() => this.regs.flags.z, false);
      d[Op.JNZ_REG] = this._makeJcc(() => !this.regs.flags.z, true);
      d[Op.JNZ_ADDR] = this._makeJcc(() => !this.regs.flags.z, false);
      d[Op.JA_REG] = this._makeJcc(
        () => !this.regs.flags.c && !this.regs.flags.z,
        true
      );
      d[Op.JA_ADDR] = this._makeJcc(
        () => !this.regs.flags.c && !this.regs.flags.z,
        false
      );
      d[Op.JNA_REG] = this._makeJcc(
        () => this.regs.flags.c || this.regs.flags.z,
        true
      );
      d[Op.JNA_ADDR] = this._makeJcc(
        () => this.regs.flags.c || this.regs.flags.z,
        false
      );
      d[Op.PUSH_REG] = (insn2) => {
        const code = this._decodeGpr(insn2.operands[0]);
        this._doPush(this.regs.read(code));
        this.regs.ip += insn2.size;
      };
      d[Op.PUSH_REGADDR] = (insn2) => {
        const addr = this._indirectAddr(insn2.operands[0]);
        this._doPush(this.mem.get(addr));
        this.regs.ip += insn2.size;
      };
      d[Op.PUSH_ADDR] = (insn2) => {
        const addr = this._directAddr(insn2.operands[0]);
        this._doPush(this.mem.get(addr));
        this.regs.ip += insn2.size;
      };
      d[Op.PUSH_CONST] = (insn2) => {
        this._doPush(insn2.operands[0]);
        this.regs.ip += insn2.size;
      };
      d[Op.POP_REG] = (insn2) => {
        const code = this._decodeGpr(insn2.operands[0]);
        this.regs.write(code, this._doPop());
        this.regs.ip += insn2.size;
      };
      d[Op.CALL_REG] = (insn2) => {
        const code = this._decodeGpr(insn2.operands[0]);
        const target = this.regs.read(code);
        this._doPush(this.regs.ip + insn2.size);
        this.regs.ip = target;
      };
      d[Op.CALL_ADDR] = (insn2) => {
        const target = insn2.operands[0];
        this._doPush(this.regs.ip + insn2.size);
        this.regs.ip = target;
      };
      d[Op.RET] = (_insn) => {
        this.regs.ip = this._doPop();
      };
      const mdReg = (i) => this._srcMuldivReg(i);
      const mdRA = (i) => this._srcMuldivRegaddr(i);
      const mdA = (i) => this._srcMuldivAddr(i);
      const mdC = (i) => this._srcMuldivConst(i);
      d[Op.MUL_REG] = this._makeMuldiv(ALU.mul, mdReg);
      d[Op.MUL_REGADDR] = this._makeMuldiv(ALU.mul, mdRA);
      d[Op.MUL_ADDR] = this._makeMuldiv(ALU.mul, mdA);
      d[Op.MUL_CONST] = this._makeMuldiv(ALU.mul, mdC);
      d[Op.DIV_REG] = this._makeDiv(mdReg);
      d[Op.DIV_REGADDR] = this._makeDiv(mdRA);
      d[Op.DIV_ADDR] = this._makeDiv(mdA);
      d[Op.DIV_CONST] = this._makeDiv(mdC);
      const srcGpr = (i) => this._srcGprReg(i);
      for (const [base, aluFn] of [
        [Op.AND_REG_REG, ALU.and_op],
        [Op.OR_REG_REG, ALU.or_op],
        [Op.XOR_REG_REG, ALU.xor_op]
      ]) {
        d[base + 0] = this._makeBitwise2op(aluFn, srcGpr);
        d[base + 1] = this._makeBitwise2op(aluFn, srcRA);
        d[base + 2] = this._makeBitwise2op(aluFn, srcA);
        d[base + 3] = this._makeBitwise2op(aluFn, srcC);
      }
      d[Op.NOT_REG] = (insn2) => {
        const code = this._decodeGpr(insn2.operands[0]);
        const [result, zero] = ALU.not_op(this.regs.read(code));
        this.regs.flags.c = false;
        this.regs.flags.z = zero;
        this.regs.write(code, result);
        this.regs.ip += insn2.size;
      };
      for (const [base, aluFn] of [[Op.SHL_REG_REG, ALU.shl], [Op.SHR_REG_REG, ALU.shr]]) {
        d[base + 0] = this._makeShift2op(aluFn, srcGpr);
        d[base + 1] = this._makeShift2op(aluFn, srcRA);
        d[base + 2] = this._makeShift2op(aluFn, srcA);
        d[base + 3] = this._makeShift2op(aluFn, srcC);
      }
    }
    // ── FPU access ─────────────────────────────────────────────────
    get _fpu() {
      const fpu = this.regs.fpu;
      if (fpu === null) {
        throw new Error("FPU not available (arch < 2)");
      }
      return fpu;
    }
    _validateFpm(fpm) {
      if (!validateFpm(fpm)) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
      }
      return decodeFpm(fpm);
    }
    // ── FP memory helpers ──────────────────────────────────────────
    _fpReadMemRaw(addr, fmt) {
      const width = FP_FMT_WIDTH[fmt];
      const nbytes = width / 8;
      const pageOffset = addr % PAGE_SIZE;
      if (pageOffset + nbytes > PAGE_SIZE) {
        throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
      }
      const data = new Uint8Array(nbytes);
      for (let i = 0; i < nbytes; i++) {
        data[i] = this.mem.get(addr + i);
      }
      return data;
    }
    _fpReadMem(addr, fmt) {
      const data = this._fpReadMemRaw(addr, fmt);
      return bytesToFloat(data, fmt);
    }
    _fpWriteMemRaw(addr, fmt, data) {
      const width = FP_FMT_WIDTH[fmt];
      const nbytes = width / 8;
      const pageOffset = addr % PAGE_SIZE;
      if (pageOffset + nbytes > PAGE_SIZE) {
        throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
      }
      for (let i = 0; i < data.length; i++) {
        this.mem.set(addr + i, data[i]);
      }
    }
    // ── FP register helpers ────────────────────────────────────────
    _fpReadReg(pos, fmt, phys = 0) {
      const raw = this._fpu.readBits(pos, fmt, phys);
      const width = FP_FMT_WIDTH[fmt];
      const data = intToBytesLE(raw, width / 8);
      return bytesToFloat(data, fmt);
    }
    _fpWriteReg(pos, fmt, value, phys = 0) {
      const { data, exc: exc2 } = floatToBytes(value, fmt, this._fpu.roundingMode);
      this._fpu.accumulateExceptions(exc2);
      const raw = intFromBytesLE(data);
      this._fpu.writeBits(pos, fmt, raw, phys);
    }
    // ── FP dispatch table ──────────────────────────────────────────
    _buildFpDispatch() {
      const d = this._dispatch;
      d[Op.FMOV_FP_ADDR] = (insn2) => {
        this._fmovLoad(insn2, this._directAddr(insn2.operands[1]));
      };
      d[Op.FMOV_FP_REGADDR] = (insn2) => {
        this._fmovLoad(insn2, this._indirectAddr(insn2.operands[1]));
      };
      d[Op.FMOV_ADDR_FP] = (insn2) => {
        this._fmovStore(insn2, this._directAddr(insn2.operands[1]));
      };
      d[Op.FMOV_REGADDR_FP] = (insn2) => {
        this._fmovStore(insn2, this._indirectAddr(insn2.operands[1]));
      };
      d[Op.FMOV_FP_IMM8] = (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        if (fmt !== FP_FMT_O3 && fmt !== FP_FMT_O2) {
          throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
        }
        this._fpu.writeBits(pos, fmt, insn2.operands[1], phys);
        this.regs.ip += insn2.size;
      };
      d[Op.FMOV_FP_IMM16] = (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        if (fmt !== FP_FMT_H && fmt !== FP_FMT_BF) {
          throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
        }
        const imm16 = insn2.operands[1] | insn2.operands[2] << 8;
        this._fpu.writeBits(pos, fmt, imm16, phys);
        this.regs.ip += insn2.size;
      };
      const dAddr = (off) => this._directAddr(off);
      const iAddr = (enc) => this._indirectAddr(enc);
      d[Op.FADD_FP_ADDR] = this._makeFpArithMem(fpAdd, dAddr);
      d[Op.FADD_FP_REGADDR] = this._makeFpArithMem(fpAdd, iAddr);
      d[Op.FSUB_FP_ADDR] = this._makeFpArithMem(fpSub, dAddr);
      d[Op.FSUB_FP_REGADDR] = this._makeFpArithMem(fpSub, iAddr);
      d[Op.FMUL_FP_ADDR] = this._makeFpArithMem(fpMul, dAddr);
      d[Op.FMUL_FP_REGADDR] = this._makeFpArithMem(fpMul, iAddr);
      d[Op.FDIV_FP_ADDR] = this._makeFpArithMem(fpDiv, dAddr);
      d[Op.FDIV_FP_REGADDR] = this._makeFpArithMem(fpDiv, iAddr);
      d[Op.FCMP_FP_ADDR] = this._makeFpCmpMem(dAddr);
      d[Op.FCMP_FP_REGADDR] = this._makeFpCmpMem(iAddr);
      d[Op.FABS_FP] = (insn2) => this._fpUnaryBitwise(insn2, fpAbs);
      d[Op.FNEG_FP] = (insn2) => this._fpUnaryBitwise(insn2, fpNeg);
      d[Op.FSQRT_FP] = (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        const val = this._fpReadReg(pos, fmt, phys);
        const { result, exc: exc2 } = fpSqrt(val, fmt, this._fpu.roundingMode);
        this._fpu.accumulateExceptions(exc2);
        this._fpWriteReg(pos, fmt, result, phys);
        this.regs.ip += insn2.size;
      };
      d[Op.FMOV_RR] = (insn2) => {
        const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn2.operands[0]);
        const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn2.operands[1]);
        if (dstFmt !== srcFmt) {
          throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
        }
        const raw = this._fpu.readBits(srcPos, srcFmt, srcPhys);
        this._fpu.writeBits(dstPos, dstFmt, raw, dstPhys);
        this.regs.ip += insn2.size;
      };
      d[Op.FCVT_FP_FP] = (insn2) => {
        const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn2.operands[0]);
        const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn2.operands[1]);
        const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
        this._fpWriteReg(dstPos, dstFmt, srcVal, dstPhys);
        this.regs.ip += insn2.size;
      };
      d[Op.FITOF_FP_GPR] = (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        const gpr = this._decodeGpr(insn2.operands[1]);
        const intVal = this.regs.read(gpr);
        this._fpWriteReg(pos, fmt, intVal, phys);
        this.regs.ip += insn2.size;
      };
      d[Op.FFTOI_GPR_FP] = (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        const gpr = this._decodeGpr(insn2.operands[1]);
        const fpVal = this._fpReadReg(pos, fmt, phys);
        let excInvalid = false;
        let excInexact = false;
        let result;
        if (Number.isNaN(fpVal)) {
          result = 0;
          excInvalid = true;
        } else if (!Number.isFinite(fpVal)) {
          result = fpVal > 0 ? 255 : 0;
          excInvalid = true;
        } else {
          const rm = this._fpu.roundingMode;
          let rounded;
          if (rm === 0) {
            rounded = Math.round(fpVal);
          } else if (rm === 1) {
            rounded = Math.trunc(fpVal);
          } else if (rm === 2) {
            rounded = Math.floor(fpVal);
          } else {
            rounded = Math.ceil(fpVal);
          }
          if (rounded !== fpVal) excInexact = true;
          if (rounded > 255) result = 255;
          else if (rounded < 0) result = 0;
          else result = rounded;
        }
        this._fpu.accumulateExceptions({
          invalid: excInvalid,
          divZero: false,
          overflow: false,
          underflow: false,
          inexact: excInexact
        });
        this.regs.write(gpr, result);
        this.regs.ip += insn2.size;
      };
      d[Op.FSTAT_GPR] = (insn2) => {
        const gpr = this._decodeGpr(insn2.operands[0]);
        this.regs.write(gpr, this._fpu.fpsr);
        this.regs.ip += insn2.size;
      };
      d[Op.FCFG_GPR] = (insn2) => {
        const gpr = this._decodeGpr(insn2.operands[0]);
        this.regs.write(gpr, this._fpu.fpcr);
        this.regs.ip += insn2.size;
      };
      d[Op.FSCFG_GPR] = (insn2) => {
        const gpr = this._decodeGpr(insn2.operands[0]);
        this._fpu.fpcr = this.regs.read(gpr) & 3;
        this.regs.ip += insn2.size;
      };
      d[Op.FCLR] = (insn2) => {
        this._fpu.fpsr = 0;
        this.regs.ip += insn2.size;
      };
      d[Op.FADD_RR] = this._makeFpArithRR(fpAdd);
      d[Op.FSUB_RR] = this._makeFpArithRR(fpSub);
      d[Op.FMUL_RR] = this._makeFpArithRR(fpMul);
      d[Op.FDIV_RR] = this._makeFpArithRR(fpDiv);
      d[Op.FCMP_RR] = (insn2) => {
        const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn2.operands[0]);
        const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn2.operands[1]);
        if (dstFmt !== srcFmt) {
          throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
        }
        const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);
        const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
        const { zero, carry, exc: exc2 } = fpCmp(dstVal, srcVal);
        this._fpu.accumulateExceptions(exc2);
        this.regs.flags.z = zero;
        this.regs.flags.c = carry;
        this.regs.ip += insn2.size;
      };
      d[Op.FCLASS_GPR_FP] = (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        const gpr = this._decodeGpr(insn2.operands[1]);
        const raw = this._fpu.readBits(pos, fmt, phys);
        const width = FP_FMT_WIDTH[fmt];
        const data = intToBytesLE(raw, width / 8);
        const val = bytesToFloat(data, fmt);
        const mask = fpClassify(val, raw, width, fmt);
        this.regs.write(gpr, mask);
        this.regs.ip += insn2.size;
      };
      d[Op.FMADD_FP_FP_ADDR] = (insn2) => {
        this._doFmadd(insn2, this._directAddr(insn2.operands[2]));
      };
      d[Op.FMADD_FP_FP_REGADDR] = (insn2) => {
        this._doFmadd(insn2, this._indirectAddr(insn2.operands[2]));
      };
    }
    // ── FP handler factories ───────────────────────────────────────
    _makeFpArithMem(arithFn, resolveAddr) {
      return (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        const addr = resolveAddr(insn2.operands[1]);
        const regVal = this._fpReadReg(pos, fmt, phys);
        const memVal = this._fpReadMem(addr, fmt);
        const { result, exc: exc2 } = arithFn(regVal, memVal, fmt, this._fpu.roundingMode);
        this._fpu.accumulateExceptions(exc2);
        this._fpWriteReg(pos, fmt, result, phys);
        this.regs.ip += insn2.size;
      };
    }
    _makeFpCmpMem(resolveAddr) {
      return (insn2) => {
        const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
        const addr = resolveAddr(insn2.operands[1]);
        const regVal = this._fpReadReg(pos, fmt, phys);
        const memVal = this._fpReadMem(addr, fmt);
        const { zero, carry, exc: exc2 } = fpCmp(regVal, memVal);
        this._fpu.accumulateExceptions(exc2);
        this.regs.flags.z = zero;
        this.regs.flags.c = carry;
        this.regs.ip += insn2.size;
      };
    }
    _makeFpArithRR(arithFn) {
      return (insn2) => {
        const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn2.operands[0]);
        const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn2.operands[1]);
        if (dstFmt !== srcFmt) {
          throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
        }
        const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);
        const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
        const { result, exc: exc2 } = arithFn(dstVal, srcVal, dstFmt, this._fpu.roundingMode);
        this._fpu.accumulateExceptions(exc2);
        this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
        this.regs.ip += insn2.size;
      };
    }
    // ── FP individual handlers ─────────────────────────────────────
    _fmovLoad(insn2, addr) {
      const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
      const data = this._fpReadMemRaw(addr, fmt);
      const raw = intFromBytesLE(data);
      this._fpu.writeBits(pos, fmt, raw, phys);
      this.regs.ip += insn2.size;
    }
    _fmovStore(insn2, addr) {
      const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
      const raw = this._fpu.readBits(pos, fmt, phys);
      const data = intToBytesLE(raw, FP_FMT_WIDTH[fmt] / 8);
      this._fpWriteMemRaw(addr, fmt, data);
      this.regs.ip += insn2.size;
    }
    _fpUnaryBitwise(insn2, fn) {
      const [phys, pos, fmt] = this._validateFpm(insn2.operands[0]);
      const raw = this._fpu.readBits(pos, fmt, phys);
      const result = fn(raw, FP_FMT_WIDTH[fmt]);
      this._fpu.writeBits(pos, fmt, result, phys);
      this.regs.ip += insn2.size;
    }
    _doFmadd(insn2, addr) {
      const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn2.operands[0]);
      const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn2.operands[1]);
      if (dstFmt !== srcFmt) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
      }
      const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
      const memVal = this._fpReadMem(addr, dstFmt);
      const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);
      const { result: mulResult, exc: mulExc } = fpMul(
        srcVal,
        memVal,
        dstFmt,
        this._fpu.roundingMode
      );
      const { result, exc: addExc } = fpAdd(
        mulResult,
        dstVal,
        dstFmt,
        this._fpu.roundingMode
      );
      this._fpu.accumulateExceptions({
        invalid: mulExc.invalid || addExc.invalid,
        divZero: mulExc.divZero || addExc.divZero,
        overflow: mulExc.overflow || addExc.overflow,
        underflow: mulExc.underflow || addExc.underflow,
        inexact: mulExc.inexact || addExc.inexact
      });
      this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
      this.regs.ip += insn2.size;
    }
  };

  // sim.js
  var STACK_BASE = SP_INIT - 2;
  var IO_BASE = IO_START;
  var WIRE_FLASH_MS = 350;
  var ALL_MNEMONICS_RE = new RegExp(
    "\\b(" + [...MNEMONICS, ...MNEMONICS_FP].join("|") + ")\\b",
    "i"
  );
  var ALL_REGISTERS_RE = new RegExp(
    "\\b(" + [...Object.keys(REGISTERS), ...Object.keys(FP_REGISTERS)].join("|") + ")\\b"
  );
  var WIRE_DATA = 0;
  var WIRE_FP = 1;
  var WIRE_IO = 2;
  var cpu = new CPU();
  var asmLabels = {};
  var asmMapping = {};
  var instrStarts = /* @__PURE__ */ new Set();
  var codeLen = 0;
  var cmView = null;
  var cmExecEffect = null;
  var cmScrollIntoView = null;
  var defaultCode = `; Simple example
; Writes Hello World to the output

        JMP start
hello:
        DB "Hello World!"    ; Variable
        DB 0                 ; String terminator

start:
        MOV C, hello         ; Point to var
        MOV D, 232           ; Point to output
        CALL print
        HLT                  ; Stop execution

print:                       ; print(C:*from, D:*to)
        PUSH A
        PUSH B
        MOV B, 0

.loop:
        MOV A, [C]           ; Get char from var
        MOV [D], A           ; Write to output
        INC C
        INC D
        CMP B, [C]           ; Check if end
        JNZ .loop            ; jump if not

        POP B
        POP A
        RET

`;
  function doAssemble(source) {
    const errEl = document.getElementById("asm-error");
    errEl.classList.add("hidden");
    errEl.textContent = "";
    try {
      const result = assemble(source);
      codeLen = result.code.length;
      asmLabels = result.labels;
      asmMapping = result.mapping;
      instrStarts = new Set(Object.keys(asmMapping).map(Number));
      cpu.reset();
      cpu.load(result.code);
      renderLabels();
      renderAll();
      return true;
    } catch (e) {
      errEl.textContent = e instanceof AsmError ? e.message : "Internal error: " + e.message;
      errEl.classList.remove("hidden");
      return false;
    }
  }
  function highlightExecLine(line) {
    if (!cmView || !cmExecEffect) return;
    cmView.dispatch({ effects: cmExecEffect.of(line) });
    if (cmScrollIntoView && line >= 1 && line <= cmView.state.doc.lines) {
      const pos = cmView.state.doc.line(line).from;
      cmView.dispatch({ effects: cmScrollIntoView(pos, { y: "center" }) });
    }
  }
  function flashWire(idx) {
    const edge = document.querySelectorAll("#wire-canvas .x6-edge")[idx];
    if (!edge) return;
    edge.classList.add("wire-active");
    setTimeout(() => edge.classList.remove("wire-active"), WIRE_FLASH_MS);
  }
  function renderAll() {
    renderCPU();
    renderFPU();
    renderMemory();
    renderDisplay();
    const line = asmMapping[cpu.ip];
    highlightExecLine(line !== void 0 ? line : -1);
  }
  function cssVar(name) {
    return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  }
  function getColors() {
    return {
      or: cssVar("--a-orange"),
      bl: cssVar("--a-blue"),
      gr: cssVar("--a-green"),
      rd: cssVar("--a-red"),
      yl: cssVar("--a-yellow"),
      dim: cssVar("--t-dim"),
      mid: cssVar("--t-mid"),
      txt: cssVar("--t-text")
    };
  }
  var colors = getColors();
  function getRegColors() {
    return { A: colors.gr, B: colors.bl, C: colors.or, D: colors.rd, IP: colors.or, SP: colors.yl, DP: colors.mid };
  }
  var regColors = getRegColors();
  function hex(v, p = 2) {
    return v.toString(16).toUpperCase().padStart(p, "0");
  }
  function printableChar(v) {
    return v >= 32 && v < 127 ? String.fromCharCode(v) : "";
  }
  var cpuFmt = "hex";
  function cpuFmtVal(v) {
    return cpuFmt === "dec" ? v.toString().padStart(3, " ") : hex(v);
  }
  function cpuStateInfo(key) {
    const k = key.toLowerCase();
    const map = {
      idle: { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><circle cx="4" cy="4" r="3" fill="currentColor"/></svg>`, color: colors.mid, title: "IDLE" },
      running: { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><polygon points="1.5,1 7,4 1.5,7" fill="currentColor"/></svg>`, color: colors.gr, title: "RUNNING" },
      halted: { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><rect x="1.5" y="1.5" width="5" height="5" rx="0.5" fill="currentColor"/></svg>`, color: colors.yl, title: "HALTED" },
      fault: { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><line x1="1.5" y1="1.5" x2="6.5" y2="6.5" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/><line x1="6.5" y1="1.5" x2="1.5" y2="6.5" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/></svg>`, color: colors.rd, title: "FAULT" }
    };
    return map[k] || map.idle;
  }
  function renderCPU() {
    const ri = (n, v) => `<div class="ri"><span class="ri-l" style="color:${regColors[n] || colors.dim}">${n}</span><span class="ri-v" style="color:${regColors[n] || colors.txt}">${cpuFmtVal(v)}</span></div>`;
    const fl = (n, v) => `<span class="fb" style="border-color:${v ? colors.or : "var(--t-border)"};color:${v ? colors.or : colors.dim};min-width:var(--s-flag-min-w);">${n}</span>`;
    document.getElementById("cpu-regs").innerHTML = ri("A", cpu.a) + ri("B", cpu.b) + ri("C", cpu.c) + ri("D", cpu.d);
    document.getElementById("cpu-ptrs").innerHTML = ri("IP", cpu.ip) + ri("SP", cpu.sp) + ri("DP", cpu.dp);
    document.getElementById("cpu-flags").innerHTML = fl("Z", cpu.zero) + fl("C", cpu.carry) + fl("F", cpu.fault);
    document.getElementById("nav-cycles").textContent = `${cpu.cycles} cycles`;
    const sc = cpuStateInfo(cpu.state);
    const si = document.getElementById("cpu-state-icon");
    si.innerHTML = sc.icon;
    si.style.color = sc.color;
    si.title = sc.title;
  }
  document.getElementById("blk-cpu").addEventListener("click", (e) => {
    const t = e.target.closest("[data-cfmt]");
    if (!t) return;
    cpuFmt = t.dataset.cfmt;
    document.querySelectorAll("#cpu-fmt-tabs .ft").forEach((b) => b.classList.toggle("act", b.dataset.cfmt === cpuFmt));
    renderCPU();
  });
  var fpuFmt = "hex";
  var _fpBuf2 = new ArrayBuffer(4);
  var _fpF322 = new Float32Array(_fpBuf2);
  var _fpU322 = new Uint32Array(_fpBuf2);
  function fpuRawBits(f) {
    _fpF322[0] = f;
    return _fpU322[0];
  }
  function renderFPUReg(bytesId, infoId, fVal, color) {
    const raw = fpuRawBits(fVal);
    const bytes = [raw >>> 24 & 255, raw >>> 16 & 255, raw >>> 8 & 255, raw & 255];
    let cells = "";
    let info = "";
    const bc = (lbl, val, span) => `<div class="ri" style="flex:${span};"><span class="ri-l" style="color:${color};font-size:7px;">${lbl}</span><span class="ri-v" style="color:${color};font-size:${val.length > 8 ? 9 : 11}px;">${val}</span></div>`;
    if (fpuFmt === "hex") {
      cells = bytes.map((b, i) => bc(`[${3 - i}]`, hex(b), 1)).join("");
      info = `= ${hex(raw, 8)}`;
    } else if (fpuFmt === "dec") {
      cells = bytes.map((b, i) => bc(`[${3 - i}]`, b.toString(), 1)).join("");
      info = `= ${raw}`;
    } else if (fpuFmt === "fp32") {
      cells = bc("f32", fVal.toPrecision(6), 4);
      info = `${hex(raw, 8)}`;
    } else if (fpuFmt === "fp16") {
      const hi16 = raw >>> 16 & 65535;
      const lo16 = raw & 65535;
      cells = bc("hi", decodeFloat16Bits(hi16).toPrecision(4), 2) + bc("lo", decodeFloat16Bits(lo16).toPrecision(4), 2);
      info = `${hex(hi16, 4)} ${hex(lo16, 4)}`;
    } else if (fpuFmt === "fp8") {
      cells = bytes.map((b, i) => bc(`[${3 - i}]`, decodeOfp8E4M3(b).toPrecision(3), 1)).join("");
      info = bytes.map((b) => hex(b)).join(" ");
    }
    document.getElementById(bytesId).innerHTML = cells;
    document.getElementById(infoId).textContent = info;
  }
  function renderFPU() {
    const fpu = cpu.fpu;
    if (!fpu) return;
    renderFPUReg("fpu-fa-bytes", "fpu-fa-info", fpu.fa, colors.gr);
    renderFPUReg("fpu-fb-bytes", "fpu-fb-info", fpu.fb, colors.bl);
    const rmNames = ["RNE", "RTZ", "RDN", "RUP"];
    const rmIdx = fpu.fpcr & 3;
    document.getElementById("fpu-rm").innerHTML = rmNames.map((n, i) => `<span class="fb ${i === rmIdx ? "fb-on" : "fb-off"}" style="font-size:8px;${i === rmIdx ? "border-color:" + colors.or + ";color:" + colors.or : ""}">${n}</span>`).join("");
    const fpsr = fpu.fpsr;
    const fl = [{ n: "NV", b: 0 }, { n: "DZ", b: 1 }, { n: "OF", b: 2 }, { n: "UF", b: 3 }, { n: "NX", b: 4 }];
    document.getElementById("fpu-flags").innerHTML = fl.map((f) => `<span class="fb ${fpsr >> f.b & 1 ? "fb-on" : "fb-off"}" style="font-size:8px;">${f.n}</span>`).join("");
  }
  document.getElementById("blk-fpu").addEventListener("click", (e) => {
    const t = e.target.closest("[data-ffmt]");
    if (!t) return;
    fpuFmt = t.dataset.ffmt;
    document.querySelectorAll("#fpu-fmt-tabs .ft").forEach((b) => b.classList.toggle("act", b.dataset.ffmt === fpuFmt));
    renderFPU();
  });
  var memFmt = "hex";
  var page = 0;
  function fmtByte(v) {
    return memFmt === "dec" ? v.toString().padStart(3, " ") : hex(v);
  }
  function cellClass(addr, val, showInstr) {
    const pageBase = page * PAGE_SIZE;
    const absAddr = pageBase + addr;
    let cl = "mem-cell";
    if (absAddr === cpu.ip) return cl + " marker-ip";
    if (absAddr === cpu.sp) return cl + " marker-sp";
    if (page === 0) {
      if (showInstr && instrStarts.has(addr)) cl += " instr-start";
      else if (showInstr && addr < codeLen && val) cl += " instr";
      else if (addr >= STACK_BASE && addr < IO_BASE) cl += " stack";
      else if (addr >= IO_BASE) cl += " io";
    }
    if (absAddr === cpu.a && absAddr !== cpu.ip) cl += " marker-a";
    if (absAddr === cpu.b && absAddr !== cpu.ip) cl += " marker-b";
    if (absAddr === cpu.c && absAddr !== cpu.ip) cl += " marker-c";
    if (absAddr === cpu.d && absAddr !== cpu.ip) cl += " marker-d";
    return cl;
  }
  function renderMemory() {
    const showInstr = document.getElementById("chk-instr").checked;
    const baseCw = parseInt(cssVar("--s-mem-cell-w")) || 28;
    const cellW = memFmt === "dec" ? baseCw + 2 : baseCw;
    const rowW = parseInt(cssVar("--s-mem-row-w")) || 24;
    const cellFont = parseInt(cssVar("--s-mem-cell-font")) || 10;
    const pageBase = page * PAGE_SIZE;
    const rows = [];
    const hdrs = Array.from({ length: 16 }, (_, c) => `<div class="mh" style="width:${cellW}px">${hex(c, 1)}</div>`).join("");
    rows.push(`<div style="display:flex;"><div class="mr" style="width:${rowW}px"></div>${hdrs}</div>`);
    for (let r = 0; r < 16; r++) {
      const cells = Array.from({ length: 16 }, (_, c) => {
        const addr = r * 16 + c;
        const absAddr = pageBase + addr;
        const val = cpu.mem.get(absAddr);
        const ch = printableChar(val);
        return `<div class="${cellClass(addr, val, showInstr)}" style="width:${cellW}px;font-size:${cellFont}px" title="[${hex(absAddr, 4)}]=${hex(val)} ${ch}">${fmtByte(val)}</div>`;
      }).join("");
      rows.push(`<div style="display:flex;"><div class="mr" style="width:${rowW}px">${hex(pageBase + r * 16, 4)}</div>${cells}</div>`);
    }
    const legend = [
      [colors.mid, "data"],
      [colors.yl, "stack"],
      [colors.gr, "i/o"],
      [colors.or, "ip"],
      [colors.yl, "sp"]
    ].map(([c, l]) => `<span><b style="color:${c};">&#9632;</b> ${l}</span>`).join("");
    document.getElementById("mem-grid").innerHTML = `<div style="line-height:0;display:inline-block;">${rows.join("")}</div><div style="margin-top:8px;display:flex;gap:12px;font-size:8px;color:${colors.dim};justify-content:center;">${legend}</div>`;
  }
  document.getElementById("chk-instr").addEventListener("change", () => renderMemory());
  document.getElementById("blk-mem").addEventListener("click", (e) => {
    const t = e.target.closest("[data-fmt]");
    if (!t) return;
    memFmt = t.dataset.fmt;
    document.querySelectorAll("#fmt-tabs .ft").forEach((b) => b.classList.toggle("act", b.dataset.fmt === memFmt));
    renderMemory();
  });
  function updatePageLabel() {
    document.getElementById("page-num").textContent = `${page}/255`;
  }
  document.getElementById("page-prev").addEventListener("click", () => {
    if (page > 0) {
      page--;
      updatePageLabel();
      renderMemory();
    }
  });
  document.getElementById("page-next").addEventListener("click", () => {
    if (page < 255) {
      page++;
      updatePageLabel();
      renderMemory();
    }
  });
  function renderDisplay() {
    let ch = "";
    for (let i = IO_BASE; i <= 255; i++) {
      const v = cpu.mem.get(i);
      const c = printableChar(v);
      ch += `<span class="cc ${c ? "on" : ""}">${c || "&nbsp;"}</span>`;
    }
    document.getElementById("disp-chars").innerHTML = `<div style="display:inline-flex;gap:1px;">${ch}</div>`;
  }
  function renderLabels() {
    const body = document.getElementById("labels-body");
    const entries = Object.entries(asmLabels).sort((a, b) => a[1] - b[1]);
    if (entries.length === 0) {
      body.innerHTML = '<tr><td colspan="4" class="py-1" style="color:var(--t-dim);">no labels</td></tr>';
      return;
    }
    body.innerHTML = entries.map(([name, addr]) => {
      const val = cpu.mem.get(addr);
      const ch = printableChar(val) ? `'${printableChar(val)}'` : "";
      return `<tr style="cursor:pointer;" data-addr="${addr}"><td class="py-1">${name}</td><td class="py-1" style="color:var(--a-orange);">${hex(addr, 4)}</td><td class="py-1">${hex(val)}</td><td class="py-1" style="color:var(--a-green);">${ch}</td></tr>`;
    }).join("");
  }
  document.getElementById("labels-body").addEventListener("click", (e) => {
    const row = e.target.closest("[data-addr]");
    if (!row) return;
    const addr = parseInt(row.dataset.addr);
    page = addr >>> 8 & 255;
    updatePageLabel();
    renderMemory();
  });
  function stepCPU() {
    if (cpu.state === CpuState.FAULT || cpu.state === CpuState.HALTED) return false;
    const prevIp = cpu.ip;
    const opcode = cpu.mem.get(prevIp);
    const wasRunning = cpu.step();
    if (BY_CODE_FP[opcode] !== void 0) {
      flashWire(WIRE_FP);
    } else {
      flashWire(WIRE_DATA);
    }
    flashWire(WIRE_IO);
    renderAll();
    return wasRunning;
  }
  function resetCPU() {
    if (runTimer) stopRun();
    cpu.reset();
    if (codeLen > 0 && cmView) {
      const source = cmView.state.doc.toString();
      try {
        const result = assemble(source);
        cpu.load(result.code);
      } catch (e) {
        console.warn("Re-assembly on reset failed:", e.message);
      }
    }
    highlightExecLine(-1);
    renderAll();
  }
  var btnRun = document.getElementById("btn-run");
  var btnStep = document.getElementById("btn-step");
  var btnReset = document.getElementById("btn-reset");
  var speedSel = document.getElementById("speed-select");
  var runTimer = null;
  function updateRunBtnColor() {
    btnRun.style.color = btnRun.dataset.state === "run" ? cssVar("--a-green") : cssVar("--a-red");
  }
  function getSpeedMs() {
    const hz = parseInt(speedSel.value) || 4;
    return Math.round(1e3 / hz);
  }
  function setRunUI(running) {
    btnRun.dataset.state = running ? "stop" : "run";
    btnRun.querySelector("svg").innerHTML = running ? '<rect x="3" y="3" width="10" height="10"/>' : '<polygon points="3,1 13,8 3,15"/>';
    btnRun.querySelector("span").textContent = running ? "stop" : "run";
    updateRunBtnColor();
  }
  function startRun() {
    if (runTimer) return;
    if (cpu.state === CpuState.HALTED || cpu.state === CpuState.FAULT) {
      resetCPU();
    }
    setRunUI(true);
    runTimer = setInterval(() => {
      if (!stepCPU()) stopRun();
    }, getSpeedMs());
  }
  function stopRun() {
    if (runTimer) {
      clearInterval(runTimer);
      runTimer = null;
    }
    if (cpu.state === CpuState.RUNNING) {
      cpu.state = CpuState.IDLE;
    }
    setRunUI(false);
    renderCPU();
  }
  btnRun.addEventListener("click", () => {
    if (runTimer) stopRun();
    else startRun();
  });
  btnStep.addEventListener("click", () => {
    if (runTimer) stopRun();
    if (cpu.state === CpuState.HALTED || cpu.state === CpuState.FAULT) return;
    stepCPU();
    if (cpu.state === CpuState.RUNNING) {
      cpu.state = CpuState.IDLE;
      renderCPU();
    }
  });
  btnReset.addEventListener("click", () => resetCPU());
  speedSel.addEventListener("change", () => {
    if (runTimer) {
      stopRun();
      startRun();
    }
  });
  document.getElementById("btn-assemble").addEventListener("click", () => {
    if (runTimer) stopRun();
    const source = cmView ? cmView.state.doc.toString() : document.querySelector("#editor-container textarea")?.value || "";
    doAssemble(source);
  });
  function updateWireColors() {
    const canvasBg = cssVar("--t-canvas");
    document.querySelectorAll("#wire-canvas rect[rx]").forEach((r) => r.setAttribute("fill", canvasBg));
    const colors2 = [cssVar("--a-yellow"), cssVar("--a-orange"), cssVar("--a-green")];
    document.querySelectorAll("#wire-canvas .x6-edge").forEach((edge, i) => {
      const c = colors2[i];
      if (!c) return;
      const line = edge.querySelector("path[stroke-dasharray]");
      if (line) line.setAttribute("stroke", c);
      edge.querySelectorAll("marker path, marker polygon").forEach((m) => {
        m.setAttribute("fill", c);
        m.setAttribute("stroke", c);
      });
      const txt = edge.querySelector("text");
      if (txt) txt.setAttribute("fill", c);
    });
  }
  var isDark = true;
  document.getElementById("btn-theme").addEventListener("click", () => {
    isDark = !isDark;
    document.documentElement.classList.toggle("light", !isDark);
    document.getElementById("theme-icon-dark").classList.toggle("hidden", isDark);
    document.getElementById("theme-icon-light").classList.toggle("hidden", !isDark);
    document.getElementById("theme-label").textContent = isDark ? "light" : "dark";
    colors = getColors();
    regColors = getRegColors();
    renderAll();
    updateRunBtnColor();
    updateWireColors();
  });
  renderAll();
  requestAnimationFrame(() => {
    const cpuEl = document.getElementById("blk-cpu");
    const fpuEl = document.getElementById("blk-fpu");
    const memEl = document.getElementById("blk-mem");
    const dispEl = document.getElementById("blk-disp");
    const wireGap = parseInt(cssVar("--s-wire-gap")) || 56;
    const cpuH = cpuEl.offsetHeight;
    const fpuH = fpuEl.offsetHeight;
    const maxH = Math.max(cpuH, fpuH);
    const topY = parseInt(cssVar("--s-top-y")) || 32;
    if (cpuH < fpuH) cpuEl.style.top = topY + Math.round((fpuH - cpuH) / 2) + "px";
    if (fpuH < cpuH) fpuEl.style.top = topY + Math.round((cpuH - fpuH) / 2) + "px";
    const topBottom = topY + maxH;
    memEl.style.top = topBottom + wireGap + "px";
    const memTop = parseInt(memEl.style.top);
    const memH = memEl.offsetHeight;
    dispEl.style.top = memTop + memH + wireGap + "px";
    const container = document.getElementById("diagram-container");
    const dispTop = parseInt(dispEl.style.top);
    container.style.height = dispTop + dispEl.offsetHeight + 32 + "px";
    initWires();
  });
  function initWires() {
    if (typeof X6 === "undefined") {
      document.getElementById("wire-canvas").innerHTML = '<div style="position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);color:#cc4444;">X6 failed to load</div>';
      return;
    }
    const container = document.getElementById("diagram-container");
    const cRect = container.getBoundingClientRect();
    const canvas = document.getElementById("wire-canvas");
    const cW = container.offsetWidth;
    const cH = container.offsetHeight;
    canvas.style.width = cW + "px";
    canvas.style.height = cH + "px";
    const { Graph } = X6;
    const graph = new Graph({
      container: canvas,
      width: cW,
      height: cH,
      background: false,
      grid: false,
      interacting: false
    });
    function portPos(portId) {
      const port = document.getElementById(portId);
      const pr = port.getBoundingClientRect();
      return {
        x: Math.round(pr.left - cRect.left + pr.width / 2),
        y: Math.round(pr.top - cRect.top + pr.height / 2)
      };
    }
    function addWire(fromId, toId, color, label, opts = {}) {
      const from = portPos(fromId);
      const to = portPos(toId);
      const bidir = opts.bidir !== false;
      const labelOffset = opts.labelOffset || 0;
      const lineAttrs = {
        stroke: color,
        strokeWidth: 1.5,
        strokeDasharray: "6 3",
        targetMarker: { name: "block", width: 6, height: 4, fill: color, stroke: color }
      };
      if (bidir) {
        lineAttrs.sourceMarker = { name: "block", width: 6, height: 4, fill: color, stroke: color };
      }
      let verts = opts.vertices || [];
      if (!opts.vertices) {
        const dx = Math.abs(to.x - from.x);
        const dy = Math.abs(to.y - from.y);
        if (dx < 4) {
        } else if (dy < 4) {
        } else {
          const midY = Math.round((from.y + to.y) / 2);
          verts = [{ x: from.x, y: midY }, { x: to.x, y: midY }];
        }
      }
      graph.addEdge({
        source: { x: from.x, y: from.y },
        target: { x: to.x, y: to.y },
        vertices: verts,
        router: { name: "normal" },
        connector: { name: "rounded", args: { radius: 8 } },
        attrs: { line: lineAttrs },
        labels: [{ position: { distance: 0.5, offset: labelOffset }, attrs: {
          text: { text: label, fontSize: 9, fontFamily: "'JetBrains Mono',monospace", fill: color, letterSpacing: "0.05em" },
          rect: { fill: cssVar("--t-canvas"), rx: 2, ry: 2 }
        } }]
      });
    }
    addWire("port-cpu-bottom", "port-mem-top", colors.yl, "data bus");
    addWire("port-cpu-right", "port-fpu-left", colors.or, "fp bus", { labelOffset: -12 });
    addWire("port-mem-bottom", "port-disp-top", colors.gr, "i/o", { bidir: false, labelOffset: 20 });
  }
  function fitDiagram() {
    const section = document.getElementById("diagram-section");
    const container = document.getElementById("diagram-container");
    const natW = parseInt(cssVar("--s-diagram-w")) || 840;
    const availW = section.clientWidth - 32;
    const scale = Math.min(availW / natW, 1);
    container.style.transform = `scale(${scale})`;
    const natH = parseInt(container.style.height) || container.offsetHeight;
    container.style.marginBottom = -(1 - scale) * natH + "px";
  }
  (() => {
    const handle = document.getElementById("split-handle");
    const left = document.getElementById("left-panel");
    let dragging = false;
    handle.addEventListener("mousedown", (e) => {
      e.preventDefault();
      dragging = true;
      handle.classList.add("active");
      document.body.style.cursor = "col-resize";
      document.body.style.userSelect = "none";
    });
    window.addEventListener("mousemove", (e) => {
      if (!dragging) return;
      const mainRect = left.parentElement.getBoundingClientRect();
      const x = e.clientX - mainRect.left;
      const pct = Math.min(Math.max(x / mainRect.width * 100, 15), 70);
      left.style.width = pct + "%";
      fitDiagram();
    });
    window.addEventListener("mouseup", () => {
      if (!dragging) return;
      dragging = false;
      handle.classList.remove("active");
      document.body.style.cursor = "";
      document.body.style.userSelect = "";
    });
    window.addEventListener("resize", fitDiagram);
    requestAnimationFrame(fitDiagram);
  })();
  (async () => {
    const ct = document.getElementById("editor-container");
    try {
      const { EditorView, basicSetup } = await import("https://esm.sh/codemirror");
      const { EditorState, StateEffect, StateField } = await import("https://esm.sh/@codemirror/state");
      const { Decoration, GutterMarker, gutter } = await import("https://esm.sh/@codemirror/view");
      const { StreamLanguage, HighlightStyle, syntaxHighlighting } = await import("https://esm.sh/@codemirror/language");
      const { tags } = await import("https://esm.sh/@lezer/highlight");
      const setExecLine = StateEffect.define();
      cmExecEffect = setExecLine;
      const execLineDeco = Decoration.line({ class: "cm-exec-line" });
      class ExecMarker extends GutterMarker {
        toDOM() {
          const el = document.createElement("span");
          el.textContent = "\u25B6";
          el.className = "cm-exec-arrow";
          return el;
        }
      }
      const execMarker = new ExecMarker();
      const execLineField = StateField.define({
        create() {
          return { line: -1, decos: Decoration.none };
        },
        update(state, tr) {
          for (const e of tr.effects) {
            if (e.is(setExecLine)) {
              if (e.value < 1) return { line: -1, decos: Decoration.none };
              const doc = tr.state.doc;
              if (e.value > doc.lines) return { line: -1, decos: Decoration.none };
              const lineStart = doc.line(e.value).from;
              return {
                line: e.value,
                decos: Decoration.set([execLineDeco.range(lineStart)])
              };
            }
          }
          return state;
        }
      });
      const execDecoExt = EditorView.decorations.from(execLineField, (s) => s.decos);
      const execGutter = gutter({
        class: "cm-exec-gutter",
        lineMarker(view, line) {
          const state = view.state.field(execLineField);
          if (state.line < 1) return null;
          const execLine = view.state.doc.line(state.line);
          return line.from === execLine.from ? execMarker : null;
        }
      });
      const asm = StreamLanguage.define({
        token(s) {
          if (s.match(/;.*/)) return "comment";
          if (s.match(ALL_MNEMONICS_RE)) return "keyword";
          if (s.match(ALL_REGISTERS_RE)) return "variableName";
          if (s.match(/\b0x[0-9A-Fa-f]+\b/)) return "number";
          if (s.match(/\b[0-9]+(\.[0-9]+)?\b/)) return "number";
          if (s.match(/'[^']*'/) || s.match(/"[^"]*"/)) return "string";
          if (s.match(/\[.*?\]/)) return "bracket";
          if (s.match(/\.?\w+:/)) return "labelName";
          s.next();
          return null;
        }
      });
      const sim8Theme = EditorView.theme({
        "&": { height: "100%", background: "var(--t-canvas)", color: "var(--t-mid)" },
        ".cm-scroller": { fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", lineHeight: "1.6" },
        ".cm-gutters": { background: "var(--t-nav)", borderRight: "1px solid var(--t-border)", color: "var(--t-dim)", minWidth: "36px" },
        ".cm-gutter": { fontSize: "11px" },
        ".cm-activeLine": { background: "rgba(204,85,0,0.04)" },
        ".cm-activeLineGutter": { background: "rgba(204,85,0,0.06)", color: "var(--t-dim)" },
        ".cm-cursor": { borderLeftColor: "var(--a-orange)", borderLeftWidth: "1.5px" },
        ".cm-selectionBackground": { background: "var(--a-orange-a20) !important" },
        ".cm-matchingBracket": { background: "var(--a-orange-a20)", color: "var(--a-orange) !important" },
        ".cm-searchMatch": { background: "var(--a-orange-a20)" },
        ".cm-foldPlaceholder": { background: "var(--t-surface)", border: "1px solid var(--t-border)", color: "var(--t-dim)" },
        ".cm-tooltip": { background: "var(--t-surface)", border: "1px solid var(--t-border)", color: "var(--t-text)" },
        ".cm-panels": { background: "var(--t-nav)", borderTop: "1px solid var(--t-border)", color: "var(--t-mid)" }
      }, { dark: true });
      const sim8Highlight = HighlightStyle.define([
        { tag: tags.keyword, class: "cm-hl-kw" },
        { tag: tags.variableName, class: "cm-hl-var" },
        { tag: tags.number, class: "cm-hl-num" },
        { tag: tags.string, class: "cm-hl-str" },
        { tag: tags.comment, class: "cm-hl-cmt" },
        { tag: tags.bracket, class: "cm-hl-brk" },
        { tag: tags.labelName, class: "cm-hl-lbl" }
      ]);
      cmScrollIntoView = EditorView.scrollIntoView;
      cmView = new EditorView({
        state: EditorState.create({ doc: defaultCode, extensions: [
          basicSetup,
          asm,
          sim8Theme,
          syntaxHighlighting(sim8Highlight),
          execLineField,
          execDecoExt,
          execGutter
        ] }),
        parent: ct
      });
    } catch (e) {
      console.warn("CodeMirror failed to load, using textarea fallback:", e);
      const ta = document.createElement("textarea");
      ta.style.cssText = "width:100%;height:100%;background:var(--t-canvas);color:var(--t-text);padding:16px;resize:none;outline:none;border:none;font-family:'JetBrains Mono',monospace;font-size:13px;tab-size:4;";
      ta.value = defaultCode;
      ta.spellcheck = false;
      ct.appendChild(ta);
    }
  })();
})();
