/**
 * Comprehensive test suite for the assembler (asm.js).
 *
 * TDD: these tests are written BEFORE asm.js exists.
 * The assembler must match the Python pysim8 assembler behavior.
 */

import { describe, it, expect } from 'vitest';
import { assemble, AsmError } from '../lib/asm.js';
import {
  Op, Reg, encodeFpm, encodeRegaddr,
  FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2,
} from '../lib/isa.js';
import { encodeFloat32, encodeFloat16 } from '../lib/fp.js';

// ── Helpers ─────────────────────────────────────────────────────────

/** Shorthand: assemble and return just the code bytes. */
function code(source, arch = 2) {
  return assemble(source, arch).code;
}

/** Shorthand: assemble expecting AsmError, return the error. */
function asmError(source, arch = 2) {
  let caught;
  try {
    assemble(source, arch);
  } catch (e) {
    caught = e;
  }
  expect(caught).toBeInstanceOf(AsmError);
  return caught;
}

// ── 1. Basic instructions ───────────────────────────────────────────

describe('basic instructions', () => {
  it('HLT', () => {
    expect(code('HLT')).toEqual([Op.HLT]);
  });

  it('MOV A, 42', () => {
    expect(code('MOV A, 42')).toEqual([Op.MOV_REG_CONST, Reg.A, 42]);
  });

  it('MOV A, B', () => {
    expect(code('MOV A, B')).toEqual([Op.MOV_REG_REG, Reg.A, Reg.B]);
  });

  it('MOV A, [0x50]', () => {
    expect(code('MOV A, [0x50]')).toEqual([Op.MOV_REG_ADDR, Reg.A, 0x50]);
  });

  it('MOV A, [B]', () => {
    const ra = encodeRegaddr(Reg.B, 0);
    expect(code('MOV A, [B]')).toEqual([Op.MOV_REG_REGADDR, Reg.A, ra]);
  });

  it('MOV A, [B+5]', () => {
    const ra = encodeRegaddr(Reg.B, 5);
    expect(code('MOV A, [B+5]')).toEqual([Op.MOV_REG_REGADDR, Reg.A, ra]);
  });

  it('MOV [0x50], A', () => {
    expect(code('MOV [0x50], A')).toEqual([Op.MOV_ADDR_REG, 0x50, Reg.A]);
  });

  it('ADD A, 10', () => {
    expect(code('ADD A, 10')).toEqual([Op.ADD_REG_CONST, Reg.A, 10]);
  });

  it('SUB A, B', () => {
    expect(code('SUB A, B')).toEqual([Op.SUB_REG_REG, Reg.A, Reg.B]);
  });

  it('CMP A, 42', () => {
    expect(code('CMP A, 42')).toEqual([Op.CMP_REG_CONST, Reg.A, 42]);
  });

  it('INC A', () => {
    expect(code('INC A')).toEqual([Op.INC_REG, Reg.A]);
  });

  it('DEC B', () => {
    expect(code('DEC B')).toEqual([Op.DEC_REG, Reg.B]);
  });

  it('JMP 0x50', () => {
    expect(code('JMP 0x50')).toEqual([Op.JMP_ADDR, 0x50]);
  });

  it('PUSH 42', () => {
    expect(code('PUSH 42')).toEqual([Op.PUSH_CONST, 42]);
  });

  it('RET', () => {
    expect(code('RET')).toEqual([Op.RET]);
  });

  it('NOT A', () => {
    expect(code('NOT A')).toEqual([Op.NOT_REG, Reg.A]);
  });
});

// ── 2. Number formats ───────────────────────────────────────────────

describe('number formats', () => {
  it('hexadecimal: MOV A, 0xFF', () => {
    expect(code('MOV A, 0xFF')).toEqual([Op.MOV_REG_CONST, Reg.A, 255]);
  });

  it('octal: MOV A, 0o77', () => {
    expect(code('MOV A, 0o77')).toEqual([Op.MOV_REG_CONST, Reg.A, 63]);
  });

  it('binary: MOV A, 11111111b', () => {
    expect(code('MOV A, 11111111b')).toEqual([Op.MOV_REG_CONST, Reg.A, 255]);
  });

  it('decimal with suffix: MOV A, 42d', () => {
    expect(code('MOV A, 42d')).toEqual([Op.MOV_REG_CONST, Reg.A, 42]);
  });

  it('char literal: MOV A, \'H\'', () => {
    expect(code("MOV A, 'H'")).toEqual([Op.MOV_REG_CONST, Reg.A, 72]);
  });

  it('zero: MOV A, 0', () => {
    expect(code('MOV A, 0')).toEqual([Op.MOV_REG_CONST, Reg.A, 0]);
  });
});

// ── 3. Labels ───────────────────────────────────────────────────────

describe('labels', () => {
  it('forward reference: JMP end / HLT / end: HLT', () => {
    // JMP end = [Op.JMP_ADDR, 3], HLT = [Op.HLT], end: HLT = [Op.HLT]
    const r = assemble('JMP end\nHLT\nend: HLT');
    expect(r.code).toEqual([Op.JMP_ADDR, 3, Op.HLT, Op.HLT]);
    expect(r.labels['end']).toBe(3);
  });

  it('backward reference: start: HLT / JMP start', () => {
    const r = assemble('start: HLT\nJMP start');
    expect(r.code).toEqual([Op.HLT, Op.JMP_ADDR, 0]);
    expect(r.labels['start']).toBe(0);
  });

  it('label in brackets: MOV A, [data] / data: DB 42', () => {
    const r = assemble('MOV A, [data]\ndata: DB 42');
    // MOV A, [data] = [Op.MOV_REG_ADDR, Reg.A, 3], data: DB 42 = [42]
    expect(r.code).toEqual([Op.MOV_REG_ADDR, Reg.A, 3, 42]);
    expect(r.labels['data']).toBe(3);
  });

  it('multiple labels', () => {
    const r = assemble('x: HLT\ny: HLT\nz: HLT');
    expect(r.labels['x']).toBe(0);
    expect(r.labels['y']).toBe(1);
    expect(r.labels['z']).toBe(2);
  });

  it('duplicate label raises AsmError', () => {
    const e = asmError('dup: HLT\ndup: HLT');
    expect(e.message).toMatch(/duplicate|already/i);
  });

  it('undefined label raises AsmError', () => {
    const e = asmError('JMP nowhere');
    expect(e.message).toMatch(/undefined/i);
  });

  it('labels are case-insensitive', () => {
    const r = assemble('MyLabel: HLT\nJMP mylabel');
    expect(r.code).toEqual([Op.HLT, Op.JMP_ADDR, 0]);
  });

  it('label-only line (no instruction)', () => {
    const r = assemble('start:\nHLT');
    expect(r.labels['start']).toBe(0);
    expect(r.code).toEqual([Op.HLT]);
  });
});

// ── 4. DB directive ─────────────────────────────────────────────────

describe('DB directive', () => {
  it('DB 1, 2, 3', () => {
    expect(code('DB 1, 2, 3')).toEqual([1, 2, 3]);
  });

  it('DB "Hello"', () => {
    expect(code('DB "Hello"')).toEqual([72, 101, 108, 108, 111]);
  });

  it('DB 0xFF', () => {
    expect(code('DB 0xFF')).toEqual([255]);
  });

  it("DB 'A'", () => {
    expect(code("DB 'A'")).toEqual([65]);
  });

  it('DB float32 (arch=2): DB 1.0', () => {
    const result = code('DB 1.0');
    const { data } = encodeFloat32(1.0);
    expect(result).toEqual(Array.from(data));
  });

  it('DB float16 suffix: DB 1.0_h', () => {
    const result = code('DB 1.0_h');
    const { data } = encodeFloat16(1.0);
    expect(result).toEqual(Array.from(data));
  });
});

// ── 5. Mnemonic aliases ─────────────────────────────────────────────

describe('mnemonic aliases', () => {
  it('JE is alias for JZ', () => {
    expect(code('JE 10')).toEqual([Op.JZ_ADDR, 10]);
  });

  it('JNE is alias for JNZ', () => {
    expect(code('JNE 10')).toEqual([Op.JNZ_ADDR, 10]);
  });
});

// ── 6. FP instructions ─────────────────────────────────────────────

describe('FP instructions', () => {
  const fpm_FA_F32 = encodeFpm(0, 0, FP_FMT_F);   // 0x00
  const fpm_FB_F32 = encodeFpm(1, 0, FP_FMT_F);   // 0x40
  const fpm_FHA_H  = encodeFpm(0, 0, FP_FMT_H);   // 0x01
  const fpm_FHB_H  = encodeFpm(0, 1, FP_FMT_H);   // 0x09

  it('FMOV.F32 FA, [0x50] -- load from address', () => {
    expect(code('FMOV.F FA, [0x50]')).toEqual([Op.FMOV_FP_ADDR, fpm_FA_F32, 0x50]);
  });

  it('FMOV.F32 [0x50], FA -- store to address', () => {
    expect(code('FMOV.F [0x50], FA')).toEqual([Op.FMOV_ADDR_FP, fpm_FA_F32, 0x50]);
  });

  it('FADD.F FA, [0x50] -- FP add from memory', () => {
    expect(code('FADD.F FA, [0x50]')).toEqual([Op.FADD_FP_ADDR, fpm_FA_F32, 0x50]);
  });

  it('FMOV.F FA, FB -- register to register', () => {
    expect(code('FMOV.F FA, FB')).toEqual([Op.FMOV_RR, fpm_FA_F32, fpm_FB_F32]);
  });

  it('FADD.H FHA, FHB -- reg-reg FP add', () => {
    expect(code('FADD.H FHA, FHB')).toEqual([Op.FADD_RR, fpm_FHA_H, fpm_FHB_H]);
  });

  it('FCVT.F.H FA, FHA -- format conversion with dual suffix', () => {
    expect(code('FCVT.F.H FA, FHA')).toEqual([Op.FCVT_FP_FP, fpm_FA_F32, fpm_FHA_H]);
  });

  it('FSTAT A -- control instruction (no suffix)', () => {
    expect(code('FSTAT A')).toEqual([Op.FSTAT_GPR, Reg.A]);
  });

  it('FCLR -- no operands, no suffix', () => {
    expect(code('FCLR')).toEqual([Op.FCLR]);
  });

  it('FABS.F FA -- unary FP', () => {
    expect(code('FABS.F FA')).toEqual([Op.FABS_FP, fpm_FA_F32]);
  });

  it('FCLASS.F A, FA -- GPR receives classification, FPM before GPR in encoding', () => {
    expect(code('FCLASS.F A, FA')).toEqual([Op.FCLASS_GPR_FP, fpm_FA_F32, Reg.A]);
  });

  it('FFTOI.F A, FA -- GPR, FP; encoding: [opcode, fpm, gpr]', () => {
    expect(code('FFTOI.F A, FA')).toEqual([Op.FFTOI_GPR_FP, fpm_FA_F32, Reg.A]);
  });

  it('FMOV.O3 FQA, 1.0 -- FP immediate 8-bit', () => {
    // FQA = phys=0, pos=0, fmt=O3
    const fpm_FQA_O3 = encodeFpm(0, 0, FP_FMT_O3);
    // 1.0 in E4M3: exp=7(bias), mant=0 → (0_0111_000)b = 0x38
    expect(code('FMOV.O3 FQA, 1.0')).toEqual([Op.FMOV_FP_IMM8, fpm_FQA_O3, 0x38]);
  });
});

// ── 7. Mapping ──────────────────────────────────────────────────────

describe('mapping (code position to source line)', () => {
  it('single instruction maps position 0 to line 1', () => {
    const r = assemble('HLT');
    expect(r.mapping[0]).toBe(1);
  });

  it('multi-line: each instruction start maps to its source line', () => {
    const r = assemble('MOV A, 1\nADD A, 2\nHLT');
    // MOV A, 1 starts at 0, line 1
    // ADD A, 2 starts at 3, line 2
    // HLT starts at 6, line 3
    expect(r.mapping[0]).toBe(1);
    expect(r.mapping[3]).toBe(2);
    expect(r.mapping[6]).toBe(3);
  });

  it('DB does not create mapping entries', () => {
    const r = assemble('DB 1, 2, 3\nHLT');
    // DB occupies positions 0,1,2 -- no mapping for those
    // HLT at position 3
    expect(r.mapping[0]).toBeUndefined();
    expect(r.mapping[3]).toBe(2);
  });
});

// ── 8. Error cases ──────────────────────────────────────────────────

describe('error cases', () => {
  it('invalid instruction: FOO A', () => {
    const e = asmError('FOO A');
    expect(e).toBeInstanceOf(AsmError);
    expect(e.message).toMatch(/invalid/i);
  });

  it('value out of range: MOV A, 256', () => {
    const e = asmError('MOV A, 256');
    expect(e).toBeInstanceOf(AsmError);
  });

  it('duplicate label', () => {
    const e = asmError('x: HLT\nx: HLT');
    expect(e).toBeInstanceOf(AsmError);
    expect(e.message).toMatch(/duplicate|already/i);
  });

  it('undefined label', () => {
    const e = asmError('JMP missing');
    expect(e).toBeInstanceOf(AsmError);
    expect(e.message).toMatch(/undefined/i);
  });

  it('wrong operand combination: MOV [0x50], [0x60]', () => {
    const e = asmError('MOV [0x50], [0x60]');
    expect(e).toBeInstanceOf(AsmError);
  });

  it('AsmError has line property', () => {
    const e = asmError('HLT\nFOO A');
    expect(e.line).toBe(2);
  });
});

// ── 9. Comments and whitespace ──────────────────────────────────────

describe('comments and whitespace', () => {
  it('inline comment ignored: MOV A, 42 ; comment', () => {
    expect(code('MOV A, 42 ; this is a comment'))
      .toEqual([Op.MOV_REG_CONST, Reg.A, 42]);
  });

  it('empty lines are ignored', () => {
    expect(code('\n\nHLT\n\n')).toEqual([Op.HLT]);
  });

  it('leading and trailing whitespace is ignored', () => {
    expect(code('   MOV A, 42   ')).toEqual([Op.MOV_REG_CONST, Reg.A, 42]);
  });

  it('comment-only lines are ignored', () => {
    expect(code('; comment\nHLT\n; another')).toEqual([Op.HLT]);
  });
});

// ── 10. Complex programs ────────────────────────────────────────────

describe('complex programs', () => {
  it('multi-instruction sequence', () => {
    expect(code('MOV A, 1\nADD A, 2\nHLT')).toEqual([
      Op.MOV_REG_CONST, Reg.A, 1,
      Op.ADD_REG_CONST, Reg.A, 2,
      Op.HLT,
    ]);
  });

  it('program with labels and conditional jump', () => {
    const src = [
      'MOV A, 5',
      'loop: DEC A',
      'JNZ loop',
      'HLT',
    ].join('\n');
    const r = assemble(src);
    expect(r.labels['loop']).toBe(3);
    // MOV A, 5 = [6, 0, 5]  (3 bytes, pos 0-2)
    // DEC A    = [19, 0]     (2 bytes, pos 3-4)
    // JNZ loop = [39, 3]     (2 bytes, pos 5-6)
    // HLT      = [0]         (1 byte,  pos 7)
    expect(r.code).toEqual([
      Op.MOV_REG_CONST, Reg.A, 5,
      Op.DEC_REG, Reg.A,
      Op.JNZ_ADDR, 3,
      Op.HLT,
    ]);
  });

  it('FP program with label reference', () => {
    const src = [
      'JMP start',
      'data: DB 0, 0, 0, 0',
      'start: FMOV.F FA, [data]',
      'HLT',
    ].join('\n');
    const r = assemble(src);
    expect(r.labels['data']).toBe(2);
    expect(r.labels['start']).toBe(6);
    // JMP start = [31, 6]
    // DB 0,0,0,0 = [0, 0, 0, 0]
    // FMOV.F FA, [data] = [128, 0x00, 2]
    // HLT = [0]
    expect(r.code).toEqual([
      Op.JMP_ADDR, 6,
      0, 0, 0, 0,
      Op.FMOV_FP_ADDR, encodeFpm(0, 0, FP_FMT_F), 2,
      Op.HLT,
    ]);
  });
});

// ── 11. Additional FP edge cases ────────────────────────────────────

describe('FP edge cases', () => {
  it('arch=1 rejects FP instructions', () => {
    const e = asmError('FADD.F FA, [0x50]', 1);
    expect(e).toBeInstanceOf(AsmError);
  });

  it('FP instruction without suffix raises error', () => {
    const e = asmError('FADD FA, [0x50]');
    expect(e.message).toMatch(/suffix/i);
  });

  it('FP suffix width mismatch with register', () => {
    // FHA is 16-bit half, but .F expects 32-bit register
    const e = asmError('FADD.F FHA, [0x50]');
    expect(e.message).toMatch(/match|width/i);
  });

  it('FCVT with identical formats is rejected', () => {
    const e = asmError('FCVT.H.H FHA, FHB');
    expect(e.message).toMatch(/identical/i);
  });

  it('FMOV.F32 FA, [B+3] -- FP with regaddr offset', () => {
    const ra = encodeRegaddr(Reg.B, 3);
    expect(code('FADD.F FA, [B+3]')).toEqual([
      Op.FADD_FP_REGADDR, encodeFpm(0, 0, FP_FMT_F), ra,
    ]);
  });

  it('case-insensitive FP register names', () => {
    expect(code('FABS.F fa')).toEqual([Op.FABS_FP, encodeFpm(0, 0, FP_FMT_F)]);
  });

  it('case-insensitive FP suffixes', () => {
    expect(code('FABS.f FA')).toEqual([Op.FABS_FP, encodeFpm(0, 0, FP_FMT_F)]);
  });
});
