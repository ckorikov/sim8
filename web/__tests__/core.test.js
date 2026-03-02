import { describe, it, expect, beforeEach } from 'vitest';
import {
  CpuState, ErrorCode, CpuFault,
  MEMORY_SIZE, PAGE_SIZE, IO_START, SP_INIT,
  Memory, CPU,
} from '../core.js';
import { encodeFloat32, decodeFloat32, encodeFloat16 } from '../fp.js';
import { Op, Reg, encodeFpm, encodeRegaddr, FP_FMT_F, FP_FMT_H, FP_FMT_O3 } from '../isa.js';

// ── Helpers ──────────────────────────────────────────────────────────

// FPM byte for FA.f32 (phys=0, pos=0, fmt=0)
const FPM_FA_F32 = encodeFpm(0, 0, FP_FMT_F);
// FPM byte for FB.f32 (phys=1, pos=0, fmt=0)
const FPM_FB_F32 = encodeFpm(1, 0, FP_FMT_F);
// FPM byte for FHA.f16 (phys=0, pos=0, fmt=1)
const FPM_FHA_F16 = encodeFpm(0, 0, FP_FMT_H);
// FPM byte for FHC.f16 (phys=1, pos=0, fmt=1)
const FPM_FHC_F16 = encodeFpm(1, 0, FP_FMT_H);

// REGADDR for B+0: ((0 & 0x1F) << 3) | 1 = 0x01
const RA_B_0 = encodeRegaddr(Reg.B, 0);
// REGADDR for A+0: ((0 & 0x1F) << 3) | 0 = 0x00
const RA_A_0 = encodeRegaddr(Reg.A, 0);

/** Store float32 LE bytes into memory at addr. */
function storeFloat32(mem, addr, value) {
  const { data } = encodeFloat32(value);
  for (let i = 0; i < 4; i++) mem.set(addr + i, data[i]);
}

/** Read float32 from memory at addr. */
function readFloat32(mem, addr) {
  const bytes = new Uint8Array(4);
  for (let i = 0; i < 4; i++) bytes[i] = mem.get(addr + i);
  return decodeFloat32(bytes);
}

// ── 1. Memory class ─────────────────────────────────────────────────

describe('Memory', () => {
  it('constructor creates 65536 zero bytes', () => {
    const mem = new Memory();
    expect(mem.get(0)).toBe(0);
    expect(mem.get(255)).toBe(0);
    expect(mem.get(65535)).toBe(0);
  });

  it('set/get reads back written byte', () => {
    const mem = new Memory();
    mem.set(100, 42);
    expect(mem.get(100)).toBe(42);
  });

  it('set masks to 0xFF', () => {
    const mem = new Memory();
    mem.set(0, 0x1FF);
    expect(mem.get(0)).toBe(0xFF);
  });

  it('load copies array into memory at offset', () => {
    const mem = new Memory();
    mem.load([10, 20, 30], 50);
    expect(mem.get(50)).toBe(10);
    expect(mem.get(51)).toBe(20);
    expect(mem.get(52)).toBe(30);
  });

  it('reset zeroes all memory', () => {
    const mem = new Memory();
    mem.set(100, 99);
    mem.reset();
    expect(mem.get(100)).toBe(0);
  });
});

// ── 2. CPU init & state machine ─────────────────────────────────────

describe('CPU init and state machine', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('constructor: state=IDLE, registers zeroed, SP=231', () => {
    expect(cpu.state).toBe(CpuState.IDLE);
    expect(cpu.a).toBe(0);
    expect(cpu.b).toBe(0);
    expect(cpu.c).toBe(0);
    expect(cpu.d).toBe(0);
    expect(cpu.sp).toBe(SP_INIT);
    expect(cpu.dp).toBe(0);
    expect(cpu.ip).toBe(0);
    expect(cpu.zero).toBe(false);
    expect(cpu.carry).toBe(false);
    expect(cpu.fault).toBe(false);
  });

  it('load resets CPU and loads code', () => {
    cpu.load([Op.MOV_REG_CONST, Reg.A, 42, Op.HLT]);
    expect(cpu.state).toBe(CpuState.IDLE);
    expect(cpu.ip).toBe(0);
    expect(cpu.mem.get(0)).toBe(Op.MOV_REG_CONST);
    expect(cpu.mem.get(3)).toBe(Op.HLT);
  });

  it('step on HALTED returns false', () => {
    cpu.load([Op.HLT]);
    cpu.step(); // IDLE -> RUNNING -> HALTED
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.step()).toBe(false);
  });

  it('step on FAULT returns false', () => {
    cpu.load([0xFF]); // invalid opcode
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.step()).toBe(false);
  });

  it('HLT transitions to HALTED', () => {
    cpu.load([Op.HLT]);
    const result = cpu.step();
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(result).toBe(false);
  });

  it('FAULT sets F flag and error code in A', () => {
    cpu.load([0xFF]); // invalid opcode
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.fault).toBe(true);
    expect(cpu.a).toBe(ErrorCode.INVALID_OPCODE);
  });

  it('reset returns to IDLE with counters zeroed', () => {
    cpu.load([Op.MOV_REG_CONST, Reg.A, 42, Op.HLT]);
    cpu.run();
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.steps).toBeGreaterThan(0);
    cpu.reset();
    expect(cpu.state).toBe(CpuState.IDLE);
    expect(cpu.steps).toBe(0);
    expect(cpu.cycles).toBe(0);
    expect(cpu.a).toBe(0);
    expect(cpu.sp).toBe(SP_INIT);
  });

  it('first step transitions IDLE to RUNNING', () => {
    // MOV A, 42 is 3 bytes -- after step IP advances
    cpu.load([Op.MOV_REG_CONST, Reg.A, 42, Op.HLT]);
    cpu.step();
    expect(cpu.state).toBe(CpuState.RUNNING);
  });
});

// ── 3. MOV instructions ─────────────────────────────────────────────

describe('MOV instructions', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('MOV A, B (reg-reg): copies B to A', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.B, 42,   // B = 42
      Op.MOV_REG_REG, Reg.A, Reg.B,  // A = B
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(42);
  });

  it('MOV A, [addr] (reg-addr): loads from DP*256+addr', () => {
    cpu.load([Op.MOV_REG_ADDR, Reg.A, 0x50, Op.HLT]);
    cpu.mem.set(0x50, 99); // DP=0, so EA = 0*256 + 0x50
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('MOV A, [B+0] (reg-regaddr): loads from indirect address', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.B, 0x50,        // B = 0x50
      Op.MOV_REG_REGADDR, Reg.A, RA_B_0,    // A = mem[DP*256 + B + 0]
      Op.HLT,
    ]);
    cpu.mem.set(0x50, 77);
    cpu.run();
    expect(cpu.a).toBe(77);
  });

  it('MOV [addr], A (addr-reg): stores A to memory', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 55,   // A = 55
      Op.MOV_ADDR_REG, 0x50, Reg.A,  // mem[0x50] = A
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.mem.get(0x50)).toBe(55);
  });

  it('MOV [B+0], A (regaddr-reg): stores A to indirect address', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 88,
      Op.MOV_REG_CONST, Reg.B, 0x50,
      Op.MOV_REGADDR_REG, RA_B_0, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.mem.get(0x50)).toBe(88);
  });

  it('MOV A, 42 (reg-const): loads immediate', () => {
    cpu.load([Op.MOV_REG_CONST, Reg.A, 42, Op.HLT]);
    cpu.run();
    expect(cpu.a).toBe(42);
  });

  it('MOV [addr], 42 (addr-const): stores immediate to memory', () => {
    cpu.load([Op.MOV_ADDR_CONST, 0x50, 42, Op.HLT]);
    cpu.run();
    expect(cpu.mem.get(0x50)).toBe(42);
  });

  it('MOV [B+0], 42 (regaddr-const): stores immediate to indirect', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.B, 0x50,
      Op.MOV_REGADDR_CONST, RA_B_0, 42,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.mem.get(0x50)).toBe(42);
  });

  it('MOV SP, 100: writes to SP register', () => {
    cpu.load([Op.MOV_REG_CONST, Reg.SP, 100, Op.HLT]);
    cpu.run();
    expect(cpu.sp).toBe(100);
  });

  it('MOV DP, 5: writes to DP register', () => {
    cpu.load([Op.MOV_REG_CONST, Reg.DP, 5, Op.HLT]);
    cpu.run();
    expect(cpu.dp).toBe(5);
  });

  it('MOV does not affect flags', () => {
    cpu.load([Op.MOV_REG_CONST, Reg.A, 0, Op.HLT]);
    cpu.run();
    expect(cpu.zero).toBe(false);
    expect(cpu.carry).toBe(false);
  });
});

// ── 4. ADD/SUB/CMP ─────────────────────────────────────────────────

describe('ADD/SUB/CMP', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('ADD A, B: 100+50=150, Z=false, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 100,
      Op.MOV_REG_CONST, Reg.B, 50,
      Op.ADD_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(150);
    expect(cpu.zero).toBe(false);
    expect(cpu.carry).toBe(false);
  });

  it('ADD with carry: 200+100=44 (mod 256), C=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 200,
      Op.MOV_REG_CONST, Reg.B, 100,
      Op.ADD_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(44);
    expect(cpu.carry).toBe(true);
  });

  it('ADD with zero result: 0+0=0, Z=true', () => {
    cpu.load([
      Op.ADD_REG_REG, Reg.A, Reg.B, // both A and B start at 0
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0);
    expect(cpu.zero).toBe(true);
  });

  it('ADD A, [B+0]: regaddr variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 10,
      Op.MOV_REG_CONST, Reg.B, 0x50,
      Op.ADD_REG_REGADDR, Reg.A, RA_B_0,
      Op.HLT,
    ]);
    cpu.mem.set(0x50, 20);
    cpu.run();
    expect(cpu.a).toBe(30);
  });

  it('ADD A, [addr]: addr variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 10,
      Op.ADD_REG_ADDR, Reg.A, 0x50,
      Op.HLT,
    ]);
    cpu.mem.set(0x50, 15);
    cpu.run();
    expect(cpu.a).toBe(25);
  });

  it('ADD A, 10: const variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 5,
      Op.ADD_REG_CONST, Reg.A, 10,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(15);
  });

  it('SUB A, B: 100-50=50', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 100,
      Op.MOV_REG_CONST, Reg.B, 50,
      Op.SUB_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(50);
    expect(cpu.carry).toBe(false);
  });

  it('SUB underflow: 10-20=246 (mod 256), C=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 10,
      Op.MOV_REG_CONST, Reg.B, 20,
      Op.SUB_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(246);
    expect(cpu.carry).toBe(true);
  });

  it('CMP equal: Z=true, C=false, A unchanged', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 50,
      Op.MOV_REG_CONST, Reg.B, 50,
      Op.CMP_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(50); // A unchanged
    expect(cpu.zero).toBe(true);
    expect(cpu.carry).toBe(false);
  });

  it('CMP less: Z=false, C=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 10,
      Op.MOV_REG_CONST, Reg.B, 50,
      Op.CMP_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(10); // A unchanged
    expect(cpu.zero).toBe(false);
    expect(cpu.carry).toBe(true);
  });

  it('CMP greater: Z=false, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 50,
      Op.MOV_REG_CONST, Reg.B, 10,
      Op.CMP_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(50);
    expect(cpu.zero).toBe(false);
    expect(cpu.carry).toBe(false);
  });

  it('CMP with const: CMP A, 42', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 42,
      Op.CMP_REG_CONST, Reg.A, 42,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.zero).toBe(true);
    expect(cpu.carry).toBe(false);
  });
});

// ── 5. INC/DEC ──────────────────────────────────────────────────────

describe('INC/DEC', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('INC A: 41 -> 42, Z=false, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 41,
      Op.INC_REG, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(42);
    expect(cpu.zero).toBe(false);
    expect(cpu.carry).toBe(false);
  });

  it('INC 255 -> 0: C=true, Z=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 255,
      Op.INC_REG, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0);
    expect(cpu.carry).toBe(true);
    expect(cpu.zero).toBe(true);
  });

  it('DEC A: 1 -> 0, Z=true, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.DEC_REG, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0);
    expect(cpu.zero).toBe(true);
    expect(cpu.carry).toBe(false);
  });

  it('DEC 0 -> 255: C=true, Z=false', () => {
    cpu.load([
      Op.DEC_REG, Reg.A, // A starts at 0
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(255);
    expect(cpu.carry).toBe(true);
    expect(cpu.zero).toBe(false);
  });
});

// ── 6. MUL/DIV ──────────────────────────────────────────────────────

describe('MUL/DIV', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('MUL reg: A=10 * B=5 -> A=50, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 10,
      Op.MOV_REG_CONST, Reg.B, 5,
      Op.MUL_REG, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(50);
    expect(cpu.carry).toBe(false);
  });

  it('MUL overflow: A=100 * 10 -> A=232, C=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 100,
      Op.MUL_CONST, 10,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe((100 * 10) & 0xFF); // 1000 & 0xFF = 232
    expect(cpu.carry).toBe(true);
  });

  it('DIV reg: A=50 / B=5 -> A=10, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 50,
      Op.MOV_REG_CONST, Reg.B, 5,
      Op.DIV_REG, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(10);
    expect(cpu.carry).toBe(false);
  });

  it('DIV by zero: FAULT(DIV_ZERO)', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 50,
      Op.DIV_CONST, 0,
      Op.HLT,
    ]);
    cpu.step(); // MOV
    cpu.step(); // DIV 0 -> FAULT
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.fault).toBe(true);
    expect(cpu.a).toBe(ErrorCode.DIV_ZERO);
  });

  it('MUL const variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 3,
      Op.MUL_CONST, 7,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(21);
  });

  it('DIV const variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 100,
      Op.DIV_CONST, 10,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(10);
  });
});

// ── 7. Jumps ────────────────────────────────────────────────────────

describe('Jump instructions', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('JMP addr: IP = target', () => {
    // Bytecode: JMP 6; <dead>; MOV A, 99; HLT
    cpu.load([
      Op.JMP_ADDR, 6,           // bytes 0-1: jump to addr 6
      Op.MOV_REG_CONST, Reg.A, 1, // bytes 2-4: should be skipped
      Op.HLT,                   // byte 5
      Op.MOV_REG_CONST, Reg.A, 99, // bytes 6-8: target
      Op.HLT,                   // byte 9
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('JMP reg: IP = register value', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.B, 9,  // B = 9
      Op.JMP_REG, Reg.B,           // jump to addr 9
      Op.MOV_REG_CONST, Reg.A, 1,  // skipped (addr 5-7)
      Op.HLT,                      // addr 8
      Op.MOV_REG_CONST, Reg.A, 99, // addr 9: target
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('JC taken: carry set -> jump', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 255,
      Op.INC_REG, Reg.A,            // A=0, C=true
      Op.JC_ADDR, 11,               // taken
      Op.MOV_REG_CONST, Reg.A, 1,   // skipped
      Op.HLT,                       // byte 10
      Op.MOV_REG_CONST, Reg.A, 99,  // byte 11: target
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('JC not taken: carry not set -> fall through', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.INC_REG, Reg.A,          // A=2, C=false
      Op.JC_ADDR, 99,             // not taken
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(2);
  });

  it('JNC taken: carry not set -> jump', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.INC_REG, Reg.A,            // A=2, C=false
      Op.JNC_ADDR, 11,              // taken
      Op.MOV_REG_CONST, Reg.A, 1,   // skipped
      Op.HLT,                       // byte 10
      Op.MOV_REG_CONST, Reg.A, 99,  // byte 11
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('JZ taken: zero set -> jump', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.DEC_REG, Reg.A,            // A=0, Z=true
      Op.JZ_ADDR, 11,               // taken
      Op.MOV_REG_CONST, Reg.A, 1,   // skipped
      Op.HLT,                       // byte 10
      Op.MOV_REG_CONST, Reg.A, 99,  // byte 11
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('JNZ taken: zero not set -> jump', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 5,
      Op.DEC_REG, Reg.A,            // A=4, Z=false
      Op.JNZ_ADDR, 11,              // taken
      Op.MOV_REG_CONST, Reg.A, 1,   // skipped
      Op.HLT,                       // byte 10
      Op.MOV_REG_CONST, Reg.A, 99,  // byte 11
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('JA taken: C=false AND Z=false -> jump (above)', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 50,
      Op.MOV_REG_CONST, Reg.B, 10,
      Op.CMP_REG_REG, Reg.A, Reg.B, // 50 > 10: Z=false, C=false
      Op.JA_ADDR, 15,               // taken → addr 15
      Op.MOV_REG_CONST, Reg.A, 1,   // skipped (addr 11-13)
      Op.HLT,                       // addr 14
      Op.MOV_REG_CONST, Reg.A, 99,  // addr 15
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });

  it('JA not taken: C=true -> not taken', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 10,
      Op.MOV_REG_CONST, Reg.B, 50,
      Op.CMP_REG_REG, Reg.A, Reg.B, // 10 < 50: C=true
      Op.JA_ADDR, 99,               // not taken
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(10);
  });

  it('JNA taken: C=true OR Z=true -> jump (not above)', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 50,
      Op.MOV_REG_CONST, Reg.B, 50,
      Op.CMP_REG_REG, Reg.A, Reg.B, // equal: Z=true
      Op.JNA_ADDR, 15,              // taken → addr 15
      Op.MOV_REG_CONST, Reg.A, 1,   // skipped (addr 11-13)
      Op.HLT,                       // addr 14
      Op.MOV_REG_CONST, Reg.A, 99,  // addr 15
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
  });
});

// ── 8. Stack ────────────────────────────────────────────────────────

describe('Stack operations', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('PUSH reg: SP decrements, value stored at old SP', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 42,
      Op.PUSH_REG, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    // PUSH: mem[SP] = val, then SP--
    expect(cpu.sp).toBe(SP_INIT - 1);
    expect(cpu.mem.get(SP_INIT)).toBe(42);
  });

  it('PUSH const: pushes immediate value', () => {
    cpu.load([
      Op.PUSH_CONST, 42,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.sp).toBe(SP_INIT - 1);
    expect(cpu.mem.get(SP_INIT)).toBe(42);
  });

  it('POP reg: SP increments, register gets value', () => {
    cpu.load([
      Op.PUSH_CONST, 42,
      Op.POP_REG, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    // POP: SP++, then A = mem[SP]
    expect(cpu.a).toBe(42);
    expect(cpu.sp).toBe(SP_INIT);
  });

  it('PUSH then POP roundtrip', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 99,
      Op.PUSH_REG, Reg.A,
      Op.MOV_REG_CONST, Reg.A, 0,
      Op.POP_REG, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(99);
    expect(cpu.sp).toBe(SP_INIT);
  });

  it('Stack overflow: SP=0, PUSH -> FAULT(STACK_OVERFLOW)', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.SP, 0,
      Op.PUSH_CONST, 42,
      Op.HLT,
    ]);
    cpu.step(); // MOV SP, 0
    cpu.step(); // PUSH -> FAULT
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.a).toBe(ErrorCode.STACK_OVERFLOW);
  });

  it('Stack underflow: SP=231, POP -> FAULT(STACK_UNDERFLOW)', () => {
    cpu.load([
      Op.POP_REG, Reg.A,
      Op.HLT,
    ]);
    // SP starts at 231
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.a).toBe(ErrorCode.STACK_UNDERFLOW);
  });

  it('CALL addr: pushes return address, jumps to target', () => {
    // Layout: CALL 8 (bytes 0-1); dead zone; HLT at byte 7; MOV A,99; HLT
    cpu.load([
      Op.CALL_ADDR, 8,              // bytes 0-1; return addr = 2
      Op.MOV_REG_CONST, Reg.A, 1,   // bytes 2-4: should be reached on RET
      Op.HLT,                       // byte 5
      0, 0,                         // padding to byte 7
      Op.MOV_REG_CONST, Reg.A, 99,  // bytes 8-10
      Op.RET,                       // byte 11
    ]);
    cpu.run();
    // After RET, IP returns to 2, runs MOV A, 1, then HLT
    expect(cpu.a).toBe(1);
    expect(cpu.sp).toBe(SP_INIT); // stack balanced
  });

  it('CALL then RET: roundtrip restores SP', () => {
    cpu.load([
      Op.CALL_ADDR, 6,         // bytes 0-1
      Op.HLT,                  // byte 2: return here
      0, 0, 0,                 // padding
      Op.RET,                  // byte 6: target
    ]);
    cpu.run();
    expect(cpu.sp).toBe(SP_INIT);
    expect(cpu.state).toBe(CpuState.HALTED);
  });
});

// ── 9. Bitwise ──────────────────────────────────────────────────────

describe('Bitwise operations', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('AND A, B: 0xFF & 0x0F = 0x0F, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0xFF,
      Op.MOV_REG_CONST, Reg.B, 0x0F,
      Op.AND_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0x0F);
    expect(cpu.carry).toBe(false);
    expect(cpu.zero).toBe(false);
  });

  it('OR A, B: 0xF0 | 0x0F = 0xFF', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0xF0,
      Op.MOV_REG_CONST, Reg.B, 0x0F,
      Op.OR_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0xFF);
    expect(cpu.carry).toBe(false);
  });

  it('XOR A, B: 0xFF ^ 0xFF = 0, Z=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0xFF,
      Op.MOV_REG_CONST, Reg.B, 0xFF,
      Op.XOR_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0);
    expect(cpu.zero).toBe(true);
    expect(cpu.carry).toBe(false);
  });

  it('NOT A: 0x55 -> 0xAA, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0x55,
      Op.NOT_REG, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0xAA);
    expect(cpu.carry).toBe(false);
  });

  it('AND zero: 0x00 & 0xFF = 0, Z=true, C=false', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.B, 0xFF,
      Op.AND_REG_REG, Reg.A, Reg.B, // A starts at 0
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0);
    expect(cpu.zero).toBe(true);
    expect(cpu.carry).toBe(false);
  });

  it('AND const variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0xFF,
      Op.AND_REG_CONST, Reg.A, 0x0F,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0x0F);
  });

  it('OR addr variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0xF0,
      Op.OR_REG_ADDR, Reg.A, 0x50,
      Op.HLT,
    ]);
    cpu.mem.set(0x50, 0x0F);
    cpu.run();
    expect(cpu.a).toBe(0xFF);
  });

  it('XOR const variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0xFF,
      Op.XOR_REG_CONST, Reg.A, 0xAA,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0x55);
  });
});

// ── 10. Shifts ──────────────────────────────────────────────────────

describe('Shift operations', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('SHL A, B: value=1, count=3 -> 8', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.MOV_REG_CONST, Reg.B, 3,
      Op.SHL_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(8);
    expect(cpu.carry).toBe(false);
  });

  it('SHL carry: 0x80 << 1 = 0, C=true, Z=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 0x80,
      Op.SHL_REG_CONST, Reg.A, 1,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0);
    expect(cpu.carry).toBe(true);
    expect(cpu.zero).toBe(true);
  });

  it('SHR A, B: value=8, count=3 -> 1', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 8,
      Op.MOV_REG_CONST, Reg.B, 3,
      Op.SHR_REG_REG, Reg.A, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(1);
    expect(cpu.carry).toBe(false);
  });

  it('SHR carry: 1 >> 1 = 0, C=true, Z=true', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.SHR_REG_CONST, Reg.A, 1,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(0);
    expect(cpu.carry).toBe(true);
    expect(cpu.zero).toBe(true);
  });

  it('SHL by 0: value unchanged', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 42,
      Op.SHL_REG_CONST, Reg.A, 0,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.a).toBe(42);
    expect(cpu.zero).toBe(false);
  });

  it('SHR addr variant', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 16,
      Op.SHR_REG_ADDR, Reg.A, 0x50,
      Op.HLT,
    ]);
    cpu.mem.set(0x50, 2);
    cpu.run();
    expect(cpu.a).toBe(4);
  });
});

// ── 11. Faults ──────────────────────────────────────────────────────

describe('Fault conditions', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('Invalid opcode: 0xFF -> FAULT(INVALID_OPCODE)', () => {
    cpu.load([0xFF]);
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.fault).toBe(true);
    expect(cpu.a).toBe(ErrorCode.INVALID_OPCODE);
  });

  it('Page boundary: instruction at IP=255 with size > 1', () => {
    // Place a 3-byte instruction at address 254
    // MOV_REG_CONST at addr 254 needs bytes at 254, 255, and 256 (out of page)
    cpu.load([Op.JMP_ADDR, 254]); // jump to 254
    cpu.mem.set(254, Op.MOV_REG_CONST);
    cpu.mem.set(255, Reg.A);
    // byte 256 is on page 1 -- page boundary fault
    cpu.step(); // JMP 254
    cpu.step(); // fetch MOV_REG_CONST at 254 -> FAULT
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.a).toBe(ErrorCode.PAGE_BOUNDARY);
  });

  it('Invalid reg: MOV with reg code 6 -> FAULT(INVALID_REG)', () => {
    cpu.load([Op.MOV_REG_CONST, 6, 42]); // reg code 6 is invalid
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.a).toBe(ErrorCode.INVALID_REG);
  });

  it('After FAULT: step() returns false', () => {
    cpu.load([0xFF]);
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.step()).toBe(false);
  });

  it('After FAULT: state=FAULT, F=true, A=error code', () => {
    cpu.load([0xFF]);
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.fault).toBe(true);
    expect(cpu.a).toBe(ErrorCode.INVALID_OPCODE);
  });

  it('FAULT from DIV 0 at known IP', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 10,
      Op.DIV_CONST, 0,
      Op.HLT,
    ]);
    cpu.step(); // MOV
    const ipBeforeDiv = cpu.ip;
    cpu.step(); // DIV 0
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.a).toBe(ErrorCode.DIV_ZERO);
  });
});

// ── 12. FPU basics ──────────────────────────────────────────────────

describe('FPU basics', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('FMOV load from memory: FA.f32 = mem[addr]', () => {
    // Store 3.0 at address 0x50
    cpu.load([Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50, Op.HLT]);
    storeFloat32(cpu.mem, 0x50, 3.0);
    cpu.run();
    expect(cpu.fpu.readBits(0, FP_FMT_F, 0)).not.toBe(0);
    // Verify value
    const val = cpu.fpu.fa;
    expect(val).toBeCloseTo(3.0, 5);
  });

  it('FMOV store to memory: mem[addr] = FA.f32', () => {
    // Load 5.0 into FA, then store to memory
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FMOV_ADDR_FP, FPM_FA_F32, 0x60,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 5.0);
    cpu.run();
    const stored = readFloat32(cpu.mem, 0x60);
    expect(stored).toBeCloseTo(5.0, 5);
  });

  it('FMOV reg-reg: copy FA to FB', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FMOV_RR, FPM_FB_F32, FPM_FA_F32,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 7.0);
    cpu.run();
    expect(cpu.fpu.fb).toBeCloseTo(7.0, 5);
  });

  it('FADD: 3.0 + 2.0 = 5.0', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,  // FA = 3.0
      Op.FADD_FP_ADDR, FPM_FA_F32, 0x60,  // FA += 2.0
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 3.0);
    storeFloat32(cpu.mem, 0x60, 2.0);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(5.0, 5);
  });

  it('FSUB: 10.0 - 3.0 = 7.0', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FSUB_FP_ADDR, FPM_FA_F32, 0x60,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 10.0);
    storeFloat32(cpu.mem, 0x60, 3.0);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(7.0, 5);
  });

  it('FMUL: 4.0 * 3.0 = 12.0', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FMUL_FP_ADDR, FPM_FA_F32, 0x60,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 4.0);
    storeFloat32(cpu.mem, 0x60, 3.0);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(12.0, 5);
  });

  it('FDIV: 10.0 / 2.0 = 5.0', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FDIV_FP_ADDR, FPM_FA_F32, 0x60,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 10.0);
    storeFloat32(cpu.mem, 0x60, 2.0);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(5.0, 5);
  });

  it('FCMP equal: Z=true', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FCMP_FP_ADDR, FPM_FA_F32, 0x60,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 3.0);
    storeFloat32(cpu.mem, 0x60, 3.0);
    cpu.run();
    expect(cpu.zero).toBe(true);
    expect(cpu.carry).toBe(false);
  });

  it('FCMP less: C=true', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FCMP_FP_ADDR, FPM_FA_F32, 0x60,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 1.0);
    storeFloat32(cpu.mem, 0x60, 3.0);
    cpu.run();
    expect(cpu.zero).toBe(false);
    expect(cpu.carry).toBe(true);
  });

  it('FABS: abs(-5.0) = 5.0', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FABS_FP, FPM_FA_F32,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, -5.0);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(5.0, 5);
  });

  it('FNEG: neg(3.0) = -3.0', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FNEG_FP, FPM_FA_F32,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 3.0);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(-3.0, 5);
  });

  it('FSQRT: sqrt(4.0) = 2.0', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FSQRT_FP, FPM_FA_F32,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 4.0);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(2.0, 5);
  });

  it('FITOF: integer 42 -> float 42.0', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 42,
      Op.FITOF_FP_GPR, FPM_FA_F32, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(42.0, 5);
  });

  it('FFTOI: float 42.0 -> integer 42', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FFTOI_GPR_FP, FPM_FA_F32, Reg.A,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 42.0);
    cpu.run();
    expect(cpu.a).toBe(42);
  });

  it('FCLR: clears FPSR', () => {
    // First trigger an exception to set FPSR, then clear it
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FDIV_FP_ADDR, FPM_FA_F32, 0x60,  // 0.0 / 0.0 -> NaN, sets invalid
      Op.FCLR,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 0.0);
    storeFloat32(cpu.mem, 0x60, 0.0);
    cpu.run();
    expect(cpu.fpu.fpsr).toBe(0);
  });

  it('FSTAT: reads FPSR into GPR', () => {
    cpu.load([
      Op.FSTAT_GPR, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    // FPSR starts at 0
    expect(cpu.a).toBe(0);
  });

  it('FCFG: reads FPCR into GPR', () => {
    cpu.load([
      Op.FCFG_GPR, Reg.A,
      Op.HLT,
    ]);
    cpu.run();
    // FPCR starts at 0
    expect(cpu.a).toBe(0);
  });

  it('FSCFG: writes GPR to FPCR', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,  // rounding mode 1 (RTZ)
      Op.FSCFG_GPR, Reg.A,
      Op.FCFG_GPR, Reg.B,
      Op.HLT,
    ]);
    cpu.run();
    expect(cpu.b).toBe(1);
    expect(cpu.fpu.fpcr).toBe(1);
  });

  it('FADD_RR: FA + FB using reg-reg', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FMOV_FP_ADDR, FPM_FB_F32, 0x60,
      Op.FADD_RR, FPM_FA_F32, FPM_FB_F32,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 1.5);
    storeFloat32(cpu.mem, 0x60, 2.5);
    cpu.run();
    expect(cpu.fpu.fa).toBeCloseTo(4.0, 5);
  });

  it('FCVT: convert between formats (FA.f32 -> FHA.f16)', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FCVT_FP_FP, FPM_FHA_F16, FPM_FA_F32,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 1.0);
    cpu.run();
    // FHA should now contain 1.0 in f16 format
    const bits = cpu.fpu.readBits(0, FP_FMT_H, 0);
    expect(bits).not.toBe(0);
  });

  it('FP_FORMAT fault: invalid FPM byte', () => {
    // FPM with phys=3 (invalid, max is 1)
    const badFpm = (3 << 6) | (0 << 3) | FP_FMT_F;
    cpu.load([Op.FMOV_FP_ADDR, badFpm, 0x50, Op.HLT]);
    cpu.step();
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.a).toBe(ErrorCode.FP_FORMAT);
  });

  it('FMOV_FP_IMM8: load 8-bit immediate', () => {
    // OFP8 E4M3 format: phys=0, pos=0, fmt=3
    const fpmQA = encodeFpm(0, 0, FP_FMT_O3);
    cpu.load([
      Op.FMOV_FP_IMM8, fpmQA, 0x3C,  // some OFP8 E4M3 value
      Op.HLT,
    ]);
    cpu.run();
    // The value was loaded (exact value depends on E4M3 decoding of 0x3C)
    expect(cpu.fpu.readBits(0, FP_FMT_O3, 0)).toBe(0x3C);
  });

  it('FCLASS: classify a value', () => {
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,
      Op.FCLASS_GPR_FP, Reg.A, FPM_FA_F32,
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 1.0);
    cpu.run();
    // Classification of 1.0 should be a non-zero category code
    expect(cpu.a).toBeGreaterThan(0);
  });

  it('FMADD: dst = src * mem + dst', () => {
    // FMADD semantics: dst = src * mem + dst
    cpu.load([
      Op.FMOV_FP_ADDR, FPM_FA_F32, 0x50,  // FA = 2.0
      Op.FMOV_FP_ADDR, FPM_FB_F32, 0x60,  // FB = 3.0
      Op.FMADD_FP_FP_ADDR, FPM_FA_F32, FPM_FB_F32, 0x70,  // FA = FB * mem[0x70] + FA
      Op.HLT,
    ]);
    storeFloat32(cpu.mem, 0x50, 2.0);
    storeFloat32(cpu.mem, 0x60, 3.0);
    storeFloat32(cpu.mem, 0x70, 1.0);
    cpu.run();
    // FA = FB(3.0) * mem(1.0) + FA(2.0) = 5.0
    expect(cpu.fpu.fa).toBeCloseTo(5.0, 5);
  });
});

// ── 13. display() ───────────────────────────────────────────────────

describe('display()', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('empty display: all zeroes -> empty string after rstrip', () => {
    cpu.load([Op.HLT]);
    cpu.run();
    const disp = cpu.display();
    expect(disp.trim()).toBe('');
  });

  it('write chars via MOV: "Hi"', () => {
    const H = 'H'.charCodeAt(0); // 72
    const i = 'i'.charCodeAt(0); // 105
    cpu.load([
      Op.MOV_ADDR_CONST, IO_START, H,
      Op.MOV_ADDR_CONST, IO_START + 1, i,
      Op.HLT,
    ]);
    cpu.run();
    const disp = cpu.display();
    expect(disp.startsWith('Hi')).toBe(true);
  });

  it('non-printable chars display as space', () => {
    cpu.load([
      Op.MOV_ADDR_CONST, IO_START, 1,     // non-printable
      Op.MOV_ADDR_CONST, IO_START + 1, 65, // 'A'
      Op.HLT,
    ]);
    cpu.run();
    const disp = cpu.display();
    // First char should be space (non-printable), second should be 'A'
    expect(disp[0]).toBe(' ');
    expect(disp[1]).toBe('A');
  });
});

// ── 14. CPU step counting ───────────────────────────────────────────

describe('CPU step counting', () => {
  let cpu;
  beforeEach(() => { cpu = new CPU(); });

  it('steps and cycles increment after each instruction', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.MOV_REG_CONST, Reg.B, 2,
      Op.HLT,
    ]);
    cpu.step(); // MOV A, 1
    expect(cpu.steps).toBe(1);
    cpu.step(); // MOV B, 2
    expect(cpu.steps).toBe(2);
    expect(cpu.cycles).toBeGreaterThanOrEqual(2);
  });

  it('HLT does not increment step count', () => {
    cpu.load([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.HLT,
    ]);
    cpu.run();
    // Only the MOV counts; HLT has cost=0
    expect(cpu.steps).toBe(1);
  });

  it('run() with maxSteps limit stops early', () => {
    // Infinite loop: JMP 0
    cpu.load([Op.JMP_ADDR, 0]);
    cpu.run(10);
    // Should have stopped after 10 steps
    expect(cpu.steps).toBe(10);
    expect(cpu.state).toBe(CpuState.RUNNING);
  });
});
