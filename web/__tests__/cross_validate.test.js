/**
 * Cross-validation: pysim8 (Python) vs web/lib (JS) on identical programs.
 *
 * For each test program, both implementations assemble and run the same
 * source code, then we compare: bytecode, final state, registers, flags,
 * cycles, display output, and FPU state.
 *
 * Requires: uv + pysim8 installed (cd ../pysim8 && uv sync).
 */

import { describe, it, expect } from 'vitest';
import { execSync } from 'node:child_process';
import { resolve } from 'node:path';

import { assemble } from '../lib/asm.js';
import { CPU, CpuState } from '../lib/core.js';
import { FP_FMT_F } from '../lib/isa.js';

// ── Helpers ──────────────────────────────────────────────────────

const PYSIM8_DIR = resolve(import.meta.dirname, '../../pysim8');

function runPython(source, arch = 2) {
  const out = execSync(
    `uv run pysim8-asm - --arch ${arch} --binary | uv run pysim8 --json -`,
    { cwd: PYSIM8_DIR, input: source, encoding: 'utf-8', timeout: 15_000, shell: true },
  );
  return JSON.parse(out);
}

function runJS(source, arch = 2) {
  const result = assemble(source, arch);
  const cpu = new CPU({ arch });
  cpu.load(result.code);
  cpu.run();

  const state = {
    code: Array.from(result.code),
    state: cpu.state,
    steps: cpu.steps,
    cycles: cpu.cycles,
    regs: {
      a: cpu.a, b: cpu.b, c: cpu.c, d: cpu.d,
      sp: cpu.sp, dp: cpu.dp, ip: cpu.ip,
    },
    flags: {
      z: cpu.zero, c: cpu.carry, f: cpu.fault,
    },
    display: cpu.display(),
  };

  if (cpu.fpu) {
    state.fpu = {
      fa: cpu.fpu.readBits(0, FP_FMT_F, 0),
      fb: cpu.fpu.readBits(0, FP_FMT_F, 1),
      fpcr: cpu.fpu.fpcr,
      fpsr: cpu.fpu.fpsr,
    };
  }

  return state;
}

function assertEquivalent(source, arch = 2) {
  const py = runPython(source, arch);
  const js = runJS(source, arch);

  expect(js.code, 'bytecode mismatch').toEqual(py.code);
  expect(js.state, 'state mismatch').toBe(py.state);
  expect(js.cycles, 'cycles mismatch').toBe(py.cycles);
  expect(js.steps, 'steps mismatch').toBe(py.steps);
  expect(js.regs, 'registers mismatch').toEqual(py.regs);
  expect(js.flags, 'flags mismatch').toEqual(py.flags);
  expect(js.display, 'display mismatch').toBe(py.display);

  if (py.fpu) {
    expect(js.fpu, 'FPU state mismatch').toEqual(py.fpu);
  }
}

// ── Integer programs ─────────────────────────────────────────────

describe('cross-validate: integer', () => {
  it('MOV immediate', () => {
    assertEquivalent(`
      MOV A, 42
      MOV B, 0xFF
      HLT
    `);
  });

  it('ADD / SUB with carry and zero', () => {
    assertEquivalent(`
      MOV A, 200
      ADD A, 100
      MOV B, A
      MOV A, 5
      SUB A, 5
      HLT
    `);
  });

  it('INC / DEC with wrap', () => {
    assertEquivalent(`
      MOV A, 255
      INC A
      MOV B, 0
      DEC B
      HLT
    `);
  });

  it('MUL / DIV', () => {
    assertEquivalent(`
      MOV A, 7
      MUL 6
      MOV B, A
      DIV 3
      HLT
    `);
  });

  it('CMP + conditional jumps', () => {
    assertEquivalent(`
      MOV A, 10
      CMP A, 10
      JZ equal
      MOV B, 1
      JMP done
      equal: MOV B, 2
      done: HLT
    `);
  });

  it('counter loop', () => {
    assertEquivalent(`
      MOV A, 0
      loop: INC A
      CMP A, 5
      JNZ loop
      HLT
    `);
  });

  it('fibonacci(5)', () => {
    assertEquivalent(`
      MOV A, 0
      MOV B, 1
      MOV C, 5
      loop: MOV D, A
      ADD A, B
      MOV B, D
      DEC C
      JNZ loop
      HLT
    `);
  });

  it('CALL / RET / stack', () => {
    assertEquivalent(`
      CALL addFive
      HLT
      addFive:
        MOV A, 10
        ADD A, 5
        RET
    `);
  });

  it('PUSH / POP', () => {
    assertEquivalent(`
      MOV A, 42
      PUSH A
      MOV A, 0
      POP A
      HLT
    `);
  });

  it('bitwise AND / OR / XOR / NOT', () => {
    assertEquivalent(`
      MOV A, 0xF0
      AND A, 0x3C
      MOV B, A
      MOV A, 0x0F
      OR A, 0xF0
      MOV C, A
      XOR C, 0xFF
      NOT C
      HLT
    `);
  });

  it('SHL / SHR', () => {
    assertEquivalent(`
      MOV A, 1
      SHL A, 4
      MOV B, A
      SHR B, 2
      HLT
    `);
  });

  it('memory direct read/write', () => {
    assertEquivalent(`
      MOV A, 99
      MOV [0x50], A
      MOV B, [0x50]
      HLT
    `);
  });

  it('register-indirect addressing', () => {
    assertEquivalent(`
      MOV C, 0x50
      MOV A, 77
      MOV [C], A
      MOV B, [C]
      HLT
    `);
  });

  it('I/O display output', () => {
    assertEquivalent(`
      MOV A, 'H'
      MOV [232], A
      MOV A, 'i'
      MOV [233], A
      HLT
    `);
  });

  it('Hello World with loop', () => {
    assertEquivalent(`
      JMP start
      hello: DB "Hello"
      DB 0
      start:
        MOV C, hello
        MOV D, 232
      loop:
        MOV A, [C]
        CMP A, 0
        JZ done
        MOV [D], A
        INC C
        INC D
        JMP loop
      done: HLT
    `);
  });

  it('nested CALL', () => {
    assertEquivalent(`
      CALL outer
      HLT
      outer:
        MOV A, 1
        CALL inner
        ADD A, 10
        RET
      inner:
        ADD A, 5
        RET
    `);
  });

  it('DB data section', () => {
    assertEquivalent(`
      JMP start
      data: DB 10, 20, 30
      start:
        MOV C, data
        MOV A, [C]
        INC C
        ADD A, [C]
        INC C
        ADD A, [C]
        HLT
    `);
  });
});

// ── Fault programs ───────────────────────────────────────────────

describe('cross-validate: faults', () => {
  it('DIV by zero → FAULT', () => {
    assertEquivalent(`
      MOV A, 10
      MOV B, 0
      DIV B
      HLT
    `);
  });

  it('invalid opcode → FAULT', () => {
    assertEquivalent(`
      DB 0xFF
    `);
  });
});

// ── FP programs ──────────────────────────────────────────────────

describe('cross-validate: FPU', () => {
  it('FITOF + FFTOI round-trip', () => {
    assertEquivalent(`
      MOV A, 42
      FITOF.F FA, A
      FFTOI.F A, FA
      HLT
    `);
  });

  it('FADD float32', () => {
    assertEquivalent(`
      MOV A, 10
      FITOF.F FA, A
      MOV A, 20
      FITOF.F FB, A
      FADD.F FA, FB
      HLT
    `);
  });

  it('FSUB float32', () => {
    assertEquivalent(`
      MOV A, 50
      FITOF.F FA, A
      MOV A, 30
      FITOF.F FB, A
      FSUB.F FA, FB
      HLT
    `);
  });

  it('FMUL float32', () => {
    assertEquivalent(`
      MOV A, 6
      FITOF.F FA, A
      MOV A, 7
      FITOF.F FB, A
      FMUL.F FA, FB
      HLT
    `);
  });

  it('FDIV float32', () => {
    assertEquivalent(`
      MOV A, 100
      FITOF.F FA, A
      MOV A, 4
      FITOF.F FB, A
      FDIV.F FA, FB
      HLT
    `);
  });

  it('FABS / FNEG', () => {
    assertEquivalent(`
      MOV A, 5
      FITOF.F FA, A
      FNEG.F FA
      FABS.F FA
      HLT
    `);
  });

  it('FCMP sets flags', () => {
    assertEquivalent(`
      MOV A, 10
      FITOF.F FA, A
      MOV A, 20
      FITOF.F FB, A
      FCMP.F FA, FB
      HLT
    `);
  });

  it('FMOV load/store memory', () => {
    assertEquivalent(`
      JMP start
      val: DB 0x00, 0x00, 0x20, 0x41
      start:
        FMOV.F FA, [val]
        FMOV.F [0x50], FA
        FMOV.F FB, [0x50]
        HLT
    `);
  });

  it('FMOV register copy', () => {
    assertEquivalent(`
      MOV A, 42
      FITOF.F FA, A
      FMOV.F FB, FA
      HLT
    `);
  });

  it('float16 arithmetic', () => {
    assertEquivalent(`
      MOV A, 3
      FITOF.H FHA, A
      MOV A, 4
      FITOF.H FHB, A
      FADD.H FHA, FHB
      FFTOI.H A, FHA
      HLT
    `);
  });

  it('FSCFG rounding mode', () => {
    assertEquivalent(`
      MOV A, 1
      FSCFG A
      MOV A, 7
      FITOF.F FA, A
      MOV A, 3
      FITOF.F FB, A
      FDIV.F FA, FB
      HLT
    `);
  });

  it('FCLASS classification', () => {
    assertEquivalent(`
      MOV A, 0
      FITOF.F FA, A
      FCLASS.F A, FA
      HLT
    `);
  });
});
