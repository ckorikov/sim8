import { describe, it, expect } from 'vitest';
import { assemble } from '../asm.js';
import { CPU, CpuState, ErrorCode } from '../core.js';

/** Assemble source, load into CPU, run, return CPU. */
function runAsm(source) {
  const { code } = assemble(source);
  const cpu = new CPU();
  cpu.load(code);
  cpu.run();
  return cpu;
}

describe('integration: integer programs', () => {
  it('1. Hello World -- write chars to I/O display', () => {
    const cpu = runAsm(`
      MOV A, 'H'
      MOV [232], A
      MOV A, 'i'
      MOV [233], A
      HLT
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.display()).toBe('Hi');
  });

  it('2. Counter -- count from 0 to 5', () => {
    const cpu = runAsm(`
      MOV A, 0
      loop: INC A
      CMP A, 5
      JNZ loop
      HLT
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(5);
    expect(cpu.zero).toBe(true);
  });

  it('3. Fibonacci -- compute fib(5) = 5', () => {
    const cpu = runAsm(`
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
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(5);
    expect(cpu.b).toBe(3);
    expect(cpu.c).toBe(0);
  });

  it('4. Stack operations -- CALL/RET subroutine', () => {
    const cpu = runAsm(`
      MOV A, 10
      CALL add_five
      HLT
      add_five: ADD A, 5
      RET
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(15);
  });

  it('5. Multiplication via loop', () => {
    const cpu = runAsm(`
      MOV B, 3
      MOV C, 4
      MOV A, 0

      loop: ADD A, B
      DEC C
      JNZ loop
      HLT
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(12);
  });

  it('6. Memory copy -- write digits to display', () => {
    const cpu = runAsm(`
      MOV [232], 48
      MOV [233], 49
      MOV [234], 50
      MOV [235], 51
      MOV [236], 52
      HLT
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.display()).toBe('01234');
  });

  it('7. Bitwise operations', () => {
    const cpu = runAsm(`
      MOV A, 0xFF
      AND A, 0x0F
      OR A, 0xF0
      XOR A, 0xAA
      NOT A
      HLT
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(0xAA);
  });

  it('8. Shifts', () => {
    const cpu = runAsm(`
      MOV A, 1
      SHL A, 4
      SHR A, 2
      HLT
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(4);
  });

  it('9. Division with remainder check', () => {
    const cpu = runAsm(`
      MOV A, 25
      DIV 7
      HLT
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(3);
  });

  it('10. Fault -- division by zero', () => {
    const cpu = runAsm(`
      MOV A, 42
      DIV 0
      HLT
    `);
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.fault).toBe(true);
    expect(cpu.a).toBe(ErrorCode.DIV_ZERO);
  });

  it('11. Stack overflow', () => {
    // Use CALL loop to recursively push nonzero return addresses.
    // PUSH A with A=0 would overwrite code with HLT (opcode 0) before SP reaches 0.
    const { code } = assemble(`
      loop: CALL loop
      HLT
    `);
    const cpu = new CPU();
    cpu.load(code);
    cpu.run(500);
    expect(cpu.state).toBe(CpuState.FAULT);
    expect(cpu.fault).toBe(true);
    expect(cpu.a).toBe(ErrorCode.STACK_OVERFLOW);
  });
});

describe('integration: FP programs', () => {
  it('12. FP load, add, store (3.0 + 2.0 = 5.0)', () => {
    const cpu = runAsm(`
      FMOV.F FA, [data1]
      FADD.F FA, [data2]
      FMOV.F [result], FA
      HLT
      data1: DB 0x00, 0x00, 0x40, 0x40
      data2: DB 0x00, 0x00, 0x00, 0x40
      result: DB 0x00, 0x00, 0x00, 0x00
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.fpu.fa).toBeCloseTo(5.0, 5);

    // Verify memory at result: 5.0 as float32 LE = 0x40A00000
    const { labels } = assemble(`
      FMOV.F FA, [data1]
      FADD.F FA, [data2]
      FMOV.F [result], FA
      HLT
      data1: DB 0x00, 0x00, 0x40, 0x40
      data2: DB 0x00, 0x00, 0x00, 0x40
      result: DB 0x00, 0x00, 0x00, 0x00
    `);
    const resultAddr = labels['result'];
    expect(cpu.mem.get(resultAddr + 0)).toBe(0x00);
    expect(cpu.mem.get(resultAddr + 1)).toBe(0x00);
    expect(cpu.mem.get(resultAddr + 2)).toBe(0xA0);
    expect(cpu.mem.get(resultAddr + 3)).toBe(0x40);
  });

  it('13. FP multiply-accumulate (3.0 * 4.0 + 2.0 = 14.0)', () => {
    const cpu = runAsm(`
      FMOV.F FA, [val1]
      FMOV.F FB, [val2]
      FMADD.F FA, FB, [val3]
      HLT
      val1: DB 2.0
      val2: DB 3.0
      val3: DB 4.0
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.fpu.fa).toBeCloseTo(14.0, 5);
  });

  it('14. FP comparison and conditional jump (3.14 > 3.0)', () => {
    const cpu = runAsm(`
      FMOV.F FA, [pi]
      FCMP.F FA, [three]
      JA greater
      MOV A, 0
      HLT
      greater: MOV A, 1
      HLT
      pi: DB 3.14
      three: DB 3.0
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(1);
  });

  it('15. Integer to float and back (FITOF + FADD + FFTOI)', () => {
    const cpu = runAsm(`
      MOV A, 42
      FITOF.F FA, A
      FADD.F FA, [quarter]
      FFTOI.F A, FA
      HLT
      quarter: DB 0.25
    `);
    expect(cpu.state).toBe(CpuState.HALTED);
    expect(cpu.a).toBe(42);
  });
});
