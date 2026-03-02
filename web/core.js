/**
 * CPU core: memory, registers, ALU, decoder, handlers, and control unit.
 * Port of pysim8/src/pysim8/sim/ into a single ES module.
 */

import {
  Op, Reg, BY_CODE, BY_CODE_FP, ISA, ISA_FP,
  decodeRegaddr, decodeFpm, validateFpm,
  FP_FMT_WIDTH, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2,
} from './isa.js';

import {
  bytesToFloat, floatToBytes,
  fpAdd, fpSub, fpMul, fpDiv, fpSqrt, fpCmp, fpAbs, fpNeg, fpClassify,
} from './fp.js';

// ── Constants ────────────────────────────────────────────────────

export const MEMORY_SIZE = 65536;
export const PAGE_SIZE = 256;
export const IO_START = 232;
export const SP_INIT = 231;

export const CpuState = Object.freeze({
  IDLE: 'IDLE',
  RUNNING: 'RUNNING',
  HALTED: 'HALTED',
  FAULT: 'FAULT',
});

export const ErrorCode = Object.freeze({
  DIV_ZERO: 1,
  STACK_OVERFLOW: 2,
  STACK_UNDERFLOW: 3,
  INVALID_REG: 4,
  PAGE_BOUNDARY: 5,
  INVALID_OPCODE: 6,
  FP_FORMAT: 12,
});

// ── CpuFault ─────────────────────────────────────────────────────

export class CpuFault extends Error {
  constructor(code, ip = 0) {
    super(`FAULT(${code}) at IP=${ip}`);
    this.code = code;
    this.ip = ip;
  }
}

// ── Memory ───────────────────────────────────────────────────────

export class Memory {
  constructor() {
    this._data = new Uint8Array(MEMORY_SIZE);
  }

  get(addr) {
    return this._data[addr];
  }

  set(addr, val) {
    this._data[addr] = val & 0xFF;
  }

  load(data, offset = 0) {
    if (offset + data.length > MEMORY_SIZE) {
      throw new RangeError(
        `Data (${data.length} bytes at offset ${offset}) exceeds memory size (${MEMORY_SIZE})`
      );
    }
    for (let i = 0; i < data.length; i++) {
      this._data[offset + i] = data[i] & 0xFF;
    }
  }

  reset() {
    this._data.fill(0);
  }
}

// ── ALU ──────────────────────────────────────────────────────────

const ALU = {
  add(a, b) {
    const raw = a + b;
    const carry = raw > 255;
    const result = raw & 0xFF;
    return [result, carry, result === 0];
  },

  sub(a, b) {
    const raw = a - b;
    const carry = raw < 0;
    const result = ((raw % 256) + 256) % 256;
    return [result, carry, result === 0];
  },

  mul(a, b) {
    const raw = a * b;
    const carry = raw > 255;
    const result = raw & 0xFF;
    return [result, carry, result === 0];
  },

  div(a, b) {
    const result = Math.floor(a / b);
    const carry = result > 255 || result < 0;
    const clamped = ((result % 256) + 256) % 256;
    return [clamped, carry, clamped === 0];
  },

  inc(a) {
    const raw = a + 1;
    const carry = raw > 255;
    const result = raw & 0xFF;
    return [result, carry, result === 0];
  },

  dec(a) {
    const raw = a - 1;
    const carry = raw < 0;
    const result = ((raw % 256) + 256) % 256;
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
    const result = a ^ 0xFF;
    return [result, result === 0];
  },

  shl(value, count) {
    const raw = value * (1 << count);
    const carry = raw > 255;
    const result = raw & 0xFF;
    return [result, carry, result === 0];
  },

  shr(value, count) {
    const carry = (value % (1 << count)) !== 0;
    const result = value >> count;
    return [result, carry, result === 0];
  },
};

// ── Flags ────────────────────────────────────────────────────────

class Flags {
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
}

// ── FpuRegisters ─────────────────────────────────────────────────

// Shared buffer for raw-bits <-> float32 conversion inside FpuRegisters
const _fpBuf = new ArrayBuffer(4);
const _fpF32 = new Float32Array(_fpBuf);
const _fpU32 = new Uint32Array(_fpBuf);

class FpuRegisters {
  constructor() {
    this._fp32 = [0, 0];
    this.fpcr = 0;
    this.fpsr = 0;
  }

  get fa() { _fpU32[0] = this._fp32[0] >>> 0; return _fpF32[0]; }
  get fb() { _fpU32[0] = this._fp32[1] >>> 0; return _fpF32[0]; }

  get roundingMode() {
    return this.fpcr & 0x03;
  }

  readBits(pos, fmt, phys = 0) {
    const width = FP_FMT_WIDTH[fmt];
    if (width === 32) {
      return this._fp32[phys] >>> 0;
    }
    const bitOffset = pos * width;
    const mask = (1 << width) - 1;
    return (this._fp32[phys] >> bitOffset) & mask;
  }

  writeBits(pos, fmt, value, phys = 0) {
    const width = FP_FMT_WIDTH[fmt];
    if (width === 32) {
      this._fp32[phys] = value >>> 0;
      return;
    }
    const bitOffset = pos * width;
    const mask = (1 << width) - 1;
    this._fp32[phys] = (
      (this._fp32[phys] & ~(mask << bitOffset))
      | ((value & mask) << bitOffset)
    ) >>> 0;
  }

  accumulateExceptions(exc) {
    if (exc.invalid) this.fpsr |= 0x01;
    if (exc.divZero) this.fpsr |= 0x02;
    if (exc.overflow) this.fpsr |= 0x04;
    if (exc.underflow) this.fpsr |= 0x08;
    if (exc.inexact) this.fpsr |= 0x10;
  }

  reset() {
    this._fp32[0] = 0;
    this._fp32[1] = 0;
    this.fpcr = 0;
    this.fpsr = 0;
  }
}

// ── RegisterFile ─────────────────────────────────────────────────

class RegisterFile {
  constructor(arch = 1) {
    this._regs = [0, 0, 0, 0, SP_INIT, 0];
    this.ip = 0;
    this.flags = new Flags();
    this.fpu = arch >= 2 ? new FpuRegisters() : null;
  }

  read(code) { return this._regs[code]; }
  write(code, val) { this._regs[code] = val & 0xFF; }

  get a() { return this._regs[0]; }
  set a(val) { this._regs[0] = val & 0xFF; }

  get b() { return this._regs[1]; }
  set b(val) { this._regs[1] = val & 0xFF; }

  get c() { return this._regs[2]; }
  set c(val) { this._regs[2] = val & 0xFF; }

  get d() { return this._regs[3]; }
  set d(val) { this._regs[3] = val & 0xFF; }

  get sp() { return this._regs[4]; }
  set sp(val) { this._regs[4] = val & 0xFF; }

  get dp() { return this._regs[5]; }
  set dp(val) { this._regs[5] = val & 0xFF; }

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
}

// ── Decoder ──────────────────────────────────────────────────────

function decode(mem, ip, arch) {
  const opcode = mem.get(ip);
  let defn = BY_CODE[opcode];
  if (defn === undefined && arch >= 2) {
    defn = BY_CODE_FP[opcode];
  }
  if (defn === undefined) {
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

// ── Byte conversion helpers ──────────────────────────────────────

function intFromBytesLE(data) {
  let raw = 0;
  for (let i = data.length - 1; i >= 0; i--) {
    raw = (raw << 8) | data[i];
  }
  if (data.length === 4) return raw >>> 0;
  return raw;
}

function intToBytesLE(raw, nbytes) {
  const data = new Uint8Array(nbytes);
  for (let i = 0; i < nbytes; i++) {
    data[i] = (raw >> (i * 8)) & 0xFF;
  }
  return data;
}

// ── CPU ──────────────────────────────────────────────────────────

export class CPU {
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

    let insn;
    try {
      insn = decode(this.mem, this.regs.ip, this._arch);
    } catch (e) {
      if (e instanceof CpuFault) {
        this._enterFault(e.code);
        return false;
      }
      throw e;
    }

    if (insn.op === Op.HLT) {
      this.state = CpuState.HALTED;
      return false;
    }

    try {
      const handler = this._dispatch[insn.op];
      handler(insn);
    } catch (e) {
      if (e instanceof CpuFault) {
        this._enterFault(e.code);
        return false;
      }
      throw e;
    }

    this._steps += 1;
    this._cycles += (this._opCost[insn.op] || 1);
    return this.state === CpuState.RUNNING;
  }

  run(maxSteps = 100000) {
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

  get steps() { return this._steps; }
  get cycles() { return this._cycles; }

  get a() { return this.regs.a; }
  get b() { return this.regs.b; }
  get c() { return this.regs.c; }
  get d() { return this.regs.d; }
  get sp() { return this.regs.sp; }
  get dp() { return this.regs.dp; }
  get ip() { return this.regs.ip; }
  get zero() { return this.regs.flags.z; }
  get carry() { return this.regs.flags.c; }
  get fault() { return this.regs.flags.f; }
  get fpu() { return this.regs.fpu; }

  display() {
    const chars = [];
    for (let addr = IO_START; addr < PAGE_SIZE; addr++) {
      const b = this.mem.get(addr);
      chars.push((b >= 0x21 && b <= 0x7E) ? String.fromCharCode(b) : ' ');
    }
    return chars.join('').trimEnd();
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

  _srcRegaddr(insn) {
    return this.mem.get(this._indirectAddr(insn.operands[1]));
  }

  _srcAddr(insn) {
    return this.mem.get(this._directAddr(insn.operands[1]));
  }

  _srcConst(insn) {
    return insn.operands[1];
  }

  _srcStkReg(insn) {
    const code = this._decodeGprOrSp(insn.operands[1]);
    return this.regs.read(code);
  }

  _srcGprReg(insn) {
    const code = this._decodeGpr(insn.operands[1]);
    return this.regs.read(code);
  }

  _srcMuldivReg(insn) {
    const code = this._decodeGpr(insn.operands[0]);
    return this.regs.read(code);
  }

  _srcMuldivRegaddr(insn) {
    return this.mem.get(this._indirectAddr(insn.operands[0]));
  }

  _srcMuldivAddr(insn) {
    return this.mem.get(this._directAddr(insn.operands[0]));
  }

  _srcMuldivConst(insn) {
    return insn.operands[0];
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
    return (insn) => {
      const destCode = this._decodeGprOrSp(insn.operands[0]);
      const right = resolveSrc(insn);
      const left = this.regs.read(destCode);
      const [result, carry, zero] = aluFn(left, right);
      this.regs.flags.c = carry;
      this.regs.flags.z = zero;
      if (writeback) {
        this.regs.write(destCode, result);
      }
      this.regs.ip += insn.size;
    };
  }

  _makeBitwise2op(aluFn, resolveSrc) {
    return (insn) => {
      const destCode = this._decodeGpr(insn.operands[0]);
      const right = resolveSrc(insn);
      const left = this.regs.read(destCode);
      const [result, zero] = aluFn(left, right);
      this.regs.flags.c = false;
      this.regs.flags.z = zero;
      this.regs.write(destCode, result);
      this.regs.ip += insn.size;
    };
  }

  _makeShift2op(aluFn, resolveSrc) {
    return (insn) => {
      const destCode = this._decodeGpr(insn.operands[0]);
      const count = resolveSrc(insn);
      const value = this.regs.read(destCode);
      if (count === 0) {
        this.regs.flags.z = value === 0;
      } else {
        const [result, carry, zero] = aluFn(value, count);
        this.regs.flags.c = carry;
        this.regs.flags.z = zero;
        this.regs.write(destCode, result);
      }
      this.regs.ip += insn.size;
    };
  }

  _makeJcc(condition, isReg) {
    return (insn) => {
      let target;
      if (isReg) {
        const code = this._decodeGpr(insn.operands[0]);
        target = this.regs.read(code);
      } else {
        target = insn.operands[0];
      }
      if (condition()) {
        this.regs.ip = target;
      } else {
        this.regs.ip += insn.size;
      }
    };
  }

  _makeMuldiv(aluFn, resolveSrc) {
    return (insn) => {
      const right = resolveSrc(insn);
      const [result, carry, zero] = aluFn(this.regs.a, right);
      this.regs.flags.c = carry;
      this.regs.flags.z = zero;
      this.regs.a = result;
      this.regs.ip += insn.size;
    };
  }

  _makeDiv(resolveSrc) {
    return (insn) => {
      const right = resolveSrc(insn);
      if (right === 0) {
        throw new CpuFault(ErrorCode.DIV_ZERO, this.regs.ip);
      }
      const [result, carry, zero] = ALU.div(this.regs.a, right);
      this.regs.flags.c = carry;
      this.regs.flags.z = zero;
      this.regs.a = result;
      this.regs.ip += insn.size;
    };
  }

  // ── Integer dispatch table ─────────────────────────────────────

  _buildDispatch() {
    const d = this._dispatch;

    // -- MOV variants --
    d[Op.MOV_REG_REG] = (insn) => {
      const dest = this._decodeMovReg(insn.operands[0]);
      const src = this._decodeMovReg(insn.operands[1]);
      this.regs.write(dest, this.regs.read(src));
      this.regs.ip += insn.size;
    };
    d[Op.MOV_REG_ADDR] = (insn) => {
      const dest = this._decodeMovReg(insn.operands[0]);
      this.regs.write(dest, this.mem.get(this._directAddr(insn.operands[1])));
      this.regs.ip += insn.size;
    };
    d[Op.MOV_REG_REGADDR] = (insn) => {
      const dest = this._decodeMovReg(insn.operands[0]);
      this.regs.write(dest, this.mem.get(this._indirectAddr(insn.operands[1])));
      this.regs.ip += insn.size;
    };
    d[Op.MOV_ADDR_REG] = (insn) => {
      const addr = this._directAddr(insn.operands[0]);
      const src = this._decodeMovReg(insn.operands[1]);
      this.mem.set(addr, this.regs.read(src));
      this.regs.ip += insn.size;
    };
    d[Op.MOV_REGADDR_REG] = (insn) => {
      const addr = this._indirectAddr(insn.operands[0]);
      const src = this._decodeMovReg(insn.operands[1]);
      this.mem.set(addr, this.regs.read(src));
      this.regs.ip += insn.size;
    };
    d[Op.MOV_REG_CONST] = (insn) => {
      const dest = this._decodeMovReg(insn.operands[0]);
      this.regs.write(dest, insn.operands[1]);
      this.regs.ip += insn.size;
    };
    d[Op.MOV_ADDR_CONST] = (insn) => {
      const addr = this._directAddr(insn.operands[0]);
      this.mem.set(addr, insn.operands[1]);
      this.regs.ip += insn.size;
    };
    d[Op.MOV_REGADDR_CONST] = (insn) => {
      const addr = this._indirectAddr(insn.operands[0]);
      this.mem.set(addr, insn.operands[1]);
      this.regs.ip += insn.size;
    };

    // -- ADD / SUB (4 variants each) --
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

    // -- INC / DEC --
    d[Op.INC_REG] = (insn) => {
      const code = this._decodeGprOrSp(insn.operands[0]);
      const [result, carry, zero] = ALU.inc(this.regs.read(code));
      this.regs.flags.c = carry;
      this.regs.flags.z = zero;
      this.regs.write(code, result);
      this.regs.ip += insn.size;
    };
    d[Op.DEC_REG] = (insn) => {
      const code = this._decodeGprOrSp(insn.operands[0]);
      const [result, carry, zero] = ALU.dec(this.regs.read(code));
      this.regs.flags.c = carry;
      this.regs.flags.z = zero;
      this.regs.write(code, result);
      this.regs.ip += insn.size;
    };

    // -- CMP (4 variants, SUB without writeback) --
    d[Op.CMP_REG_REG] = this._makeAlu2op(ALU.sub, srcStk, false);
    d[Op.CMP_REG_REGADDR] = this._makeAlu2op(ALU.sub, srcRA, false);
    d[Op.CMP_REG_ADDR] = this._makeAlu2op(ALU.sub, srcA, false);
    d[Op.CMP_REG_CONST] = this._makeAlu2op(ALU.sub, srcC, false);

    // -- JMP --
    d[Op.JMP_REG] = (insn) => {
      const code = this._decodeGpr(insn.operands[0]);
      this.regs.ip = this.regs.read(code);
    };
    d[Op.JMP_ADDR] = (insn) => {
      this.regs.ip = insn.operands[0];
    };

    // -- Conditional jumps --
    d[Op.JC_REG] = this._makeJcc(() => this.regs.flags.c, true);
    d[Op.JC_ADDR] = this._makeJcc(() => this.regs.flags.c, false);
    d[Op.JNC_REG] = this._makeJcc(() => !this.regs.flags.c, true);
    d[Op.JNC_ADDR] = this._makeJcc(() => !this.regs.flags.c, false);
    d[Op.JZ_REG] = this._makeJcc(() => this.regs.flags.z, true);
    d[Op.JZ_ADDR] = this._makeJcc(() => this.regs.flags.z, false);
    d[Op.JNZ_REG] = this._makeJcc(() => !this.regs.flags.z, true);
    d[Op.JNZ_ADDR] = this._makeJcc(() => !this.regs.flags.z, false);
    d[Op.JA_REG] = this._makeJcc(
      () => !this.regs.flags.c && !this.regs.flags.z, true
    );
    d[Op.JA_ADDR] = this._makeJcc(
      () => !this.regs.flags.c && !this.regs.flags.z, false
    );
    d[Op.JNA_REG] = this._makeJcc(
      () => this.regs.flags.c || this.regs.flags.z, true
    );
    d[Op.JNA_ADDR] = this._makeJcc(
      () => this.regs.flags.c || this.regs.flags.z, false
    );

    // -- PUSH (4 variants) --
    d[Op.PUSH_REG] = (insn) => {
      const code = this._decodeGpr(insn.operands[0]);
      this._doPush(this.regs.read(code));
      this.regs.ip += insn.size;
    };
    d[Op.PUSH_REGADDR] = (insn) => {
      const addr = this._indirectAddr(insn.operands[0]);
      this._doPush(this.mem.get(addr));
      this.regs.ip += insn.size;
    };
    d[Op.PUSH_ADDR] = (insn) => {
      const addr = this._directAddr(insn.operands[0]);
      this._doPush(this.mem.get(addr));
      this.regs.ip += insn.size;
    };
    d[Op.PUSH_CONST] = (insn) => {
      this._doPush(insn.operands[0]);
      this.regs.ip += insn.size;
    };

    // -- POP --
    d[Op.POP_REG] = (insn) => {
      const code = this._decodeGpr(insn.operands[0]);
      this.regs.write(code, this._doPop());
      this.regs.ip += insn.size;
    };

    // -- CALL / RET --
    d[Op.CALL_REG] = (insn) => {
      const code = this._decodeGpr(insn.operands[0]);
      const target = this.regs.read(code);
      this._doPush(this.regs.ip + insn.size);
      this.regs.ip = target;
    };
    d[Op.CALL_ADDR] = (insn) => {
      const target = insn.operands[0];
      this._doPush(this.regs.ip + insn.size);
      this.regs.ip = target;
    };
    d[Op.RET] = (_insn) => {
      this.regs.ip = this._doPop();
    };

    // -- MUL (4 variants) --
    const mdReg = (i) => this._srcMuldivReg(i);
    const mdRA = (i) => this._srcMuldivRegaddr(i);
    const mdA = (i) => this._srcMuldivAddr(i);
    const mdC = (i) => this._srcMuldivConst(i);

    d[Op.MUL_REG] = this._makeMuldiv(ALU.mul, mdReg);
    d[Op.MUL_REGADDR] = this._makeMuldiv(ALU.mul, mdRA);
    d[Op.MUL_ADDR] = this._makeMuldiv(ALU.mul, mdA);
    d[Op.MUL_CONST] = this._makeMuldiv(ALU.mul, mdC);

    // -- DIV (4 variants) --
    d[Op.DIV_REG] = this._makeDiv(mdReg);
    d[Op.DIV_REGADDR] = this._makeDiv(mdRA);
    d[Op.DIV_ADDR] = this._makeDiv(mdA);
    d[Op.DIV_CONST] = this._makeDiv(mdC);

    // -- Bitwise: AND/OR/XOR (4 variants each) --
    const srcGpr = (i) => this._srcGprReg(i);

    for (const [base, aluFn] of [
      [Op.AND_REG_REG, ALU.and_op],
      [Op.OR_REG_REG, ALU.or_op],
      [Op.XOR_REG_REG, ALU.xor_op],
    ]) {
      d[base + 0] = this._makeBitwise2op(aluFn, srcGpr);
      d[base + 1] = this._makeBitwise2op(aluFn, srcRA);
      d[base + 2] = this._makeBitwise2op(aluFn, srcA);
      d[base + 3] = this._makeBitwise2op(aluFn, srcC);
    }

    // -- NOT --
    d[Op.NOT_REG] = (insn) => {
      const code = this._decodeGpr(insn.operands[0]);
      const [result, zero] = ALU.not_op(this.regs.read(code));
      this.regs.flags.c = false;
      this.regs.flags.z = zero;
      this.regs.write(code, result);
      this.regs.ip += insn.size;
    };

    // -- Shift: SHL/SHR (4 variants each) --
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
      throw new Error('FPU not available (arch < 2)');
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
    const { data, exc } = floatToBytes(value, fmt, this._fpu.roundingMode);
    this._fpu.accumulateExceptions(exc);
    const raw = intFromBytesLE(data);
    this._fpu.writeBits(pos, fmt, raw, phys);
  }

  // ── FP dispatch table ──────────────────────────────────────────

  _buildFpDispatch() {
    const d = this._dispatch;

    // -- FMOV load/store (128-131) --
    d[Op.FMOV_FP_ADDR] = (insn) => {
      this._fmovLoad(insn, this._directAddr(insn.operands[1]));
    };
    d[Op.FMOV_FP_REGADDR] = (insn) => {
      this._fmovLoad(insn, this._indirectAddr(insn.operands[1]));
    };
    d[Op.FMOV_ADDR_FP] = (insn) => {
      this._fmovStore(insn, this._directAddr(insn.operands[1]));
    };
    d[Op.FMOV_REGADDR_FP] = (insn) => {
      this._fmovStore(insn, this._indirectAddr(insn.operands[1]));
    };

    // -- FMOV immediate (161-162) --
    d[Op.FMOV_FP_IMM8] = (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      if (fmt !== FP_FMT_O3 && fmt !== FP_FMT_O2) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
      }
      this._fpu.writeBits(pos, fmt, insn.operands[1], phys);
      this.regs.ip += insn.size;
    };
    d[Op.FMOV_FP_IMM16] = (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      if (fmt !== FP_FMT_H && fmt !== FP_FMT_BF) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
      }
      const imm16 = insn.operands[1] | (insn.operands[2] << 8);
      this._fpu.writeBits(pos, fmt, imm16, phys);
      this.regs.ip += insn.size;
    };

    // -- FP arith mem (132-141) --
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

    // -- Unary (142-144) --
    d[Op.FABS_FP] = (insn) => this._fpUnaryBitwise(insn, fpAbs);
    d[Op.FNEG_FP] = (insn) => this._fpUnaryBitwise(insn, fpNeg);
    d[Op.FSQRT_FP] = (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      const val = this._fpReadReg(pos, fmt, phys);
      const { result, exc } = fpSqrt(val, fmt, this._fpu.roundingMode);
      this._fpu.accumulateExceptions(exc);
      this._fpWriteReg(pos, fmt, result, phys);
      this.regs.ip += insn.size;
    };

    // -- FMOV reg-reg (145) --
    d[Op.FMOV_RR] = (insn) => {
      const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn.operands[0]);
      const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn.operands[1]);
      if (dstFmt !== srcFmt) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
      }
      const raw = this._fpu.readBits(srcPos, srcFmt, srcPhys);
      this._fpu.writeBits(dstPos, dstFmt, raw, dstPhys);
      this.regs.ip += insn.size;
    };

    // -- FCVT (146) --
    d[Op.FCVT_FP_FP] = (insn) => {
      const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn.operands[0]);
      const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn.operands[1]);
      const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
      this._fpWriteReg(dstPos, dstFmt, srcVal, dstPhys);
      this.regs.ip += insn.size;
    };

    // -- FITOF (147) --
    d[Op.FITOF_FP_GPR] = (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      const gpr = this._decodeGpr(insn.operands[1]);
      const intVal = this.regs.read(gpr);
      this._fpWriteReg(pos, fmt, intVal, phys);
      this.regs.ip += insn.size;
    };

    // -- FFTOI (148) --
    d[Op.FFTOI_GPR_FP] = (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      const gpr = this._decodeGpr(insn.operands[1]);
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
        if (rm === 0) {       // RNE
          rounded = Math.round(fpVal);
        } else if (rm === 1) { // RTZ
          rounded = Math.trunc(fpVal);
        } else if (rm === 2) { // RDN
          rounded = Math.floor(fpVal);
        } else {               // RUP
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
        inexact: excInexact,
      });
      this.regs.write(gpr, result);
      this.regs.ip += insn.size;
    };

    // -- FSTAT (149) --
    d[Op.FSTAT_GPR] = (insn) => {
      const gpr = this._decodeGpr(insn.operands[0]);
      this.regs.write(gpr, this._fpu.fpsr);
      this.regs.ip += insn.size;
    };

    // -- FCFG (150) --
    d[Op.FCFG_GPR] = (insn) => {
      const gpr = this._decodeGpr(insn.operands[0]);
      this.regs.write(gpr, this._fpu.fpcr);
      this.regs.ip += insn.size;
    };

    // -- FSCFG (151) --
    d[Op.FSCFG_GPR] = (insn) => {
      const gpr = this._decodeGpr(insn.operands[0]);
      this._fpu.fpcr = this.regs.read(gpr) & 0x03;
      this.regs.ip += insn.size;
    };

    // -- FCLR (152) --
    d[Op.FCLR] = (insn) => {
      this._fpu.fpsr = 0;
      this.regs.ip += insn.size;
    };

    // -- Reg-reg arith (153-156) --
    d[Op.FADD_RR] = this._makeFpArithRR(fpAdd);
    d[Op.FSUB_RR] = this._makeFpArithRR(fpSub);
    d[Op.FMUL_RR] = this._makeFpArithRR(fpMul);
    d[Op.FDIV_RR] = this._makeFpArithRR(fpDiv);

    // -- FCMP_RR (157) --
    d[Op.FCMP_RR] = (insn) => {
      const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn.operands[0]);
      const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn.operands[1]);
      if (dstFmt !== srcFmt) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
      }
      const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);
      const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
      const { zero, carry, exc } = fpCmp(dstVal, srcVal);
      this._fpu.accumulateExceptions(exc);
      this.regs.flags.z = zero;
      this.regs.flags.c = carry;
      this.regs.ip += insn.size;
    };

    // -- FCLASS (158) --
    d[Op.FCLASS_GPR_FP] = (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      const gpr = this._decodeGpr(insn.operands[1]);
      const raw = this._fpu.readBits(pos, fmt, phys);
      const width = FP_FMT_WIDTH[fmt];
      const data = intToBytesLE(raw, width / 8);
      const val = bytesToFloat(data, fmt);
      const mask = fpClassify(val, raw, width, fmt);
      this.regs.write(gpr, mask);
      this.regs.ip += insn.size;
    };

    // -- FMADD (159-160) --
    d[Op.FMADD_FP_FP_ADDR] = (insn) => {
      this._doFmadd(insn, this._directAddr(insn.operands[2]));
    };
    d[Op.FMADD_FP_FP_REGADDR] = (insn) => {
      this._doFmadd(insn, this._indirectAddr(insn.operands[2]));
    };
  }

  // ── FP handler factories ───────────────────────────────────────

  _makeFpArithMem(arithFn, resolveAddr) {
    return (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      const addr = resolveAddr(insn.operands[1]);
      const regVal = this._fpReadReg(pos, fmt, phys);
      const memVal = this._fpReadMem(addr, fmt);
      const { result, exc } = arithFn(regVal, memVal, fmt, this._fpu.roundingMode);
      this._fpu.accumulateExceptions(exc);
      this._fpWriteReg(pos, fmt, result, phys);
      this.regs.ip += insn.size;
    };
  }

  _makeFpCmpMem(resolveAddr) {
    return (insn) => {
      const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
      const addr = resolveAddr(insn.operands[1]);
      const regVal = this._fpReadReg(pos, fmt, phys);
      const memVal = this._fpReadMem(addr, fmt);
      const { zero, carry, exc } = fpCmp(regVal, memVal);
      this._fpu.accumulateExceptions(exc);
      this.regs.flags.z = zero;
      this.regs.flags.c = carry;
      this.regs.ip += insn.size;
    };
  }

  _makeFpArithRR(arithFn) {
    return (insn) => {
      const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn.operands[0]);
      const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn.operands[1]);
      if (dstFmt !== srcFmt) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
      }
      const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);
      const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
      const { result, exc } = arithFn(dstVal, srcVal, dstFmt, this._fpu.roundingMode);
      this._fpu.accumulateExceptions(exc);
      this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
      this.regs.ip += insn.size;
    };
  }

  // ── FP individual handlers ─────────────────────────────────────

  _fmovLoad(insn, addr) {
    const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
    const data = this._fpReadMemRaw(addr, fmt);
    const raw = intFromBytesLE(data);
    this._fpu.writeBits(pos, fmt, raw, phys);
    this.regs.ip += insn.size;
  }

  _fmovStore(insn, addr) {
    const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
    const raw = this._fpu.readBits(pos, fmt, phys);
    const data = intToBytesLE(raw, FP_FMT_WIDTH[fmt] / 8);
    this._fpWriteMemRaw(addr, fmt, data);
    this.regs.ip += insn.size;
  }

  _fpUnaryBitwise(insn, fn) {
    const [phys, pos, fmt] = this._validateFpm(insn.operands[0]);
    const raw = this._fpu.readBits(pos, fmt, phys);
    const result = fn(raw, FP_FMT_WIDTH[fmt]);
    this._fpu.writeBits(pos, fmt, result, phys);
    this.regs.ip += insn.size;
  }

  _doFmadd(insn, addr) {
    const [dstPhys, dstPos, dstFmt] = this._validateFpm(insn.operands[0]);
    const [srcPhys, srcPos, srcFmt] = this._validateFpm(insn.operands[1]);
    if (dstFmt !== srcFmt) {
      throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
    }

    const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
    const memVal = this._fpReadMem(addr, dstFmt);
    const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);

    const { result: mulResult, exc: mulExc } = fpMul(
      srcVal, memVal, dstFmt, this._fpu.roundingMode,
    );
    const { result, exc: addExc } = fpAdd(
      mulResult, dstVal, dstFmt, this._fpu.roundingMode,
    );

    this._fpu.accumulateExceptions({
      invalid: mulExc.invalid || addExc.invalid,
      divZero: mulExc.divZero || addExc.divZero,
      overflow: mulExc.overflow || addExc.overflow,
      underflow: mulExc.underflow || addExc.underflow,
      inexact: mulExc.inexact || addExc.inexact,
    });
    this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
    this.regs.ip += insn.size;
  }
}
