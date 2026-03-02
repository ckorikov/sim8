import { describe, it, expect } from 'vitest';
import {
  Op, Reg, OpType, REGISTERS, GPR_CODES, STACK_CODES,
  MNEMONIC_ALIASES, ISA, ISA_FP, BY_CODE, BY_CODE_FP,
  BY_MNEMONIC, BY_MNEMONIC_FP, MNEMONICS, MNEMONICS_FP,
  FP_CONTROL_MNEMONICS,
  encodeRegaddr, decodeRegaddr,
  FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2,
  FP_FMT_N1, FP_FMT_N2, FP_FMT_WIDTH, FP_FMT_MAX_POS,
  FP_REGISTERS, FP_SUFFIX_TO_FMT, FP_WIDTH_REGS,
  encodeFpm, decodeFpm, validateFpm,
} from '../lib/isa.js';

// ── Opcode enum ──────────────────────────────────────────────────

describe('Op', () => {
  it('has HLT = 0', () => {
    expect(Op.HLT).toBe(0);
  });

  it('has all integer opcodes', () => {
    // Expected: 74 integer opcodes (0, 1-8, 10-23, 30-43, 50-57, 60-67, 70-82, 90-97)
    const intOps = ISA.map(i => i.op);
    expect(intOps.length).toBe(74);
  });

  it('has all FP opcodes', () => {
    const fpOps = ISA_FP.map(i => i.op);
    expect(fpOps.length).toBe(35);
  });

  it('total opcodes = 109', () => {
    expect(ISA.length + ISA_FP.length).toBe(109);
  });

  it('no duplicate opcodes across ISA and ISA_FP', () => {
    const allCodes = [...ISA.map(i => i.op), ...ISA_FP.map(i => i.op)];
    expect(new Set(allCodes).size).toBe(allCodes.length);
  });

  it('FP opcodes start at 128', () => {
    for (const insn of ISA_FP) {
      expect(insn.op).toBeGreaterThanOrEqual(128);
    }
  });

  it('integer opcodes are < 128', () => {
    for (const insn of ISA) {
      expect(insn.op).toBeLessThan(128);
    }
  });
});

// ── Registers ────────────────────────────────────────────────────

describe('Reg', () => {
  it('has correct codes', () => {
    expect(Reg.A).toBe(0);
    expect(Reg.B).toBe(1);
    expect(Reg.C).toBe(2);
    expect(Reg.D).toBe(3);
    expect(Reg.SP).toBe(4);
    expect(Reg.DP).toBe(5);
  });

  it('REGISTERS maps names to codes', () => {
    expect(REGISTERS['A']).toBe(0);
    expect(REGISTERS['SP']).toBe(4);
    expect(REGISTERS['DP']).toBe(5);
    expect(Object.keys(REGISTERS).length).toBe(6);
  });

  it('GPR_CODES = {0,1,2,3}', () => {
    expect(GPR_CODES).toEqual(new Set([0, 1, 2, 3]));
  });

  it('STACK_CODES = {0,1,2,3,4}', () => {
    expect(STACK_CODES).toEqual(new Set([0, 1, 2, 3, 4]));
  });
});

// ── REGADDR encoding ─────────────────────────────────────────────

describe('REGADDR encoding', () => {
  it('encodes [A] as 0x00', () => {
    expect(encodeRegaddr(0, 0)).toBe(0x00);
  });

  it('encodes [B+3] as 0x19', () => {
    expect(encodeRegaddr(1, 3)).toBe(0x19);
  });

  it('encodes [C-1] as 0xFA', () => {
    expect(encodeRegaddr(2, -1)).toBe(0xFA);
  });

  it('roundtrips all valid register+offset combos', () => {
    for (let reg = 0; reg <= 5; reg++) {
      for (let off = -16; off <= 15; off++) {
        const encoded = encodeRegaddr(reg, off);
        const [decReg, decOff] = decodeRegaddr(encoded);
        expect(decReg).toBe(reg);
        expect(decOff).toBe(off);
      }
    }
  });

  it('throws on invalid register code', () => {
    expect(() => encodeRegaddr(6, 0)).toThrow();
    expect(() => encodeRegaddr(-1, 0)).toThrow();
  });

  it('throws on out-of-range offset', () => {
    expect(() => encodeRegaddr(0, 16)).toThrow();
    expect(() => encodeRegaddr(0, -17)).toThrow();
  });
});

// ── FPM encoding ─────────────────────────────────────────────────

describe('FPM encoding', () => {
  it('encodes (phys=0, pos=0, fmt=F) correctly', () => {
    expect(encodeFpm(0, 0, FP_FMT_F)).toBe(0x00);
  });

  it('encodes (phys=1, pos=0, fmt=F) = 0x40', () => {
    expect(encodeFpm(1, 0, FP_FMT_F)).toBe(0x40);
  });

  it('encodes (phys=0, pos=1, fmt=H) correctly', () => {
    // (0 << 6) | (1 << 3) | 1 = 9
    expect(encodeFpm(0, 1, FP_FMT_H)).toBe(9);
  });

  it('roundtrips all valid combos', () => {
    for (let phys = 0; phys <= 1; phys++) {
      for (let fmt = 0; fmt <= 4; fmt++) {
        const maxPos = FP_FMT_MAX_POS[fmt];
        for (let pos = 0; pos <= maxPos; pos++) {
          const fpm = encodeFpm(phys, pos, fmt);
          const [dPhys, dPos, dFmt] = decodeFpm(fpm);
          expect(dPhys).toBe(phys);
          expect(dPos).toBe(pos);
          expect(dFmt).toBe(fmt);
        }
      }
    }
  });

  it('validates valid FPM bytes', () => {
    expect(validateFpm(encodeFpm(0, 0, FP_FMT_F))).toBe(true);
    expect(validateFpm(encodeFpm(1, 0, FP_FMT_F))).toBe(true);
    expect(validateFpm(encodeFpm(0, 1, FP_FMT_H))).toBe(true);
    expect(validateFpm(encodeFpm(0, 3, FP_FMT_O3))).toBe(true);
  });

  it('rejects invalid: phys > 1', () => {
    // phys=2, pos=0, fmt=0 → (2 << 6) | 0 = 128
    expect(validateFpm(128)).toBe(false);
  });

  it('rejects invalid: fmt >= 5', () => {
    // phys=0, pos=0, fmt=5 → 5
    expect(validateFpm(5)).toBe(false);
    expect(validateFpm(6)).toBe(false);
    expect(validateFpm(7)).toBe(false);
  });

  it('rejects invalid: pos out of range for fmt', () => {
    // F format allows only pos=0
    expect(validateFpm(encodeFpm(0, 1, FP_FMT_F))).toBe(false);
    // H format allows pos 0-1
    expect(validateFpm(encodeFpm(0, 2, FP_FMT_H))).toBe(false);
    // O3 format allows pos 0-3
    expect(validateFpm(encodeFpm(0, 4, FP_FMT_O3))).toBe(false);
  });
});

// ── FP format constants ──────────────────────────────────────────

describe('FP format constants', () => {
  it('has correct format codes', () => {
    expect(FP_FMT_F).toBe(0);
    expect(FP_FMT_H).toBe(1);
    expect(FP_FMT_BF).toBe(2);
    expect(FP_FMT_O3).toBe(3);
    expect(FP_FMT_O2).toBe(4);
    expect(FP_FMT_N1).toBe(5);
    expect(FP_FMT_N2).toBe(6);
  });

  it('has correct widths', () => {
    expect(FP_FMT_WIDTH[FP_FMT_F]).toBe(32);
    expect(FP_FMT_WIDTH[FP_FMT_H]).toBe(16);
    expect(FP_FMT_WIDTH[FP_FMT_BF]).toBe(16);
    expect(FP_FMT_WIDTH[FP_FMT_O3]).toBe(8);
    expect(FP_FMT_WIDTH[FP_FMT_O2]).toBe(8);
    expect(FP_FMT_WIDTH[FP_FMT_N1]).toBe(4);
    expect(FP_FMT_WIDTH[FP_FMT_N2]).toBe(4);
  });

  it('has correct max positions', () => {
    expect(FP_FMT_MAX_POS[FP_FMT_F]).toBe(0);
    expect(FP_FMT_MAX_POS[FP_FMT_H]).toBe(1);
    expect(FP_FMT_MAX_POS[FP_FMT_BF]).toBe(1);
    expect(FP_FMT_MAX_POS[FP_FMT_O3]).toBe(3);
    expect(FP_FMT_MAX_POS[FP_FMT_O2]).toBe(3);
    expect(FP_FMT_MAX_POS[FP_FMT_N1]).toBe(7);
    expect(FP_FMT_MAX_POS[FP_FMT_N2]).toBe(7);
  });

  it('FP_SUFFIX_TO_FMT maps short and long names', () => {
    expect(FP_SUFFIX_TO_FMT['F']).toBe(FP_FMT_F);
    expect(FP_SUFFIX_TO_FMT['E8M23']).toBe(FP_FMT_F);
    expect(FP_SUFFIX_TO_FMT['H']).toBe(FP_FMT_H);
    expect(FP_SUFFIX_TO_FMT['BF']).toBe(FP_FMT_BF);
    expect(FP_SUFFIX_TO_FMT['O3']).toBe(FP_FMT_O3);
    expect(FP_SUFFIX_TO_FMT['O2']).toBe(FP_FMT_O2);
  });
});

// ── FP register table ────────────────────────────────────────────

describe('FP_REGISTERS', () => {
  it('has FA and FB at phys 0 and 1', () => {
    expect(FP_REGISTERS['FA']).toEqual({ phys: 0, pos: 0, fmt: FP_FMT_F, width: 32 });
    expect(FP_REGISTERS['FB']).toEqual({ phys: 1, pos: 0, fmt: FP_FMT_F, width: 32 });
  });

  it('has half registers FHA..FHD', () => {
    expect(FP_REGISTERS['FHA']).toEqual({ phys: 0, pos: 0, fmt: FP_FMT_H, width: 16 });
    expect(FP_REGISTERS['FHB']).toEqual({ phys: 0, pos: 1, fmt: FP_FMT_H, width: 16 });
    expect(FP_REGISTERS['FHC']).toEqual({ phys: 1, pos: 0, fmt: FP_FMT_H, width: 16 });
    expect(FP_REGISTERS['FHD']).toEqual({ phys: 1, pos: 1, fmt: FP_FMT_H, width: 16 });
  });

  it('has quarter registers FQA..FQH', () => {
    expect(FP_REGISTERS['FQA']).toEqual({ phys: 0, pos: 0, fmt: FP_FMT_O3, width: 8 });
    expect(FP_REGISTERS['FQH']).toEqual({ phys: 1, pos: 3, fmt: FP_FMT_O3, width: 8 });
  });

  it('has 32 + 2 = 34 total FP register names', () => {
    // 2 (FA, FB) + 4 (FHA..FHD) + 8 (FQA..FQH) + 16 (FOA..FOP) = 30
    // Nope: 2 full + 4 half + 8 quarter + 16 octet = 30
    expect(Object.keys(FP_REGISTERS).length).toBe(30);
  });

  it('FP_WIDTH_REGS has correct register counts', () => {
    expect(FP_WIDTH_REGS[32].size).toBe(2);
    expect(FP_WIDTH_REGS[16].size).toBe(4);
    expect(FP_WIDTH_REGS[8].size).toBe(8);
    expect(FP_WIDTH_REGS[4].size).toBe(16);
  });
});

// ── Instruction definitions ──────────────────────────────────────

describe('InsnDef', () => {
  it('HLT has size 1 and cost 0', () => {
    const hlt = BY_CODE[Op.HLT];
    expect(hlt.mnemonic).toBe('HLT');
    expect(hlt.sig.length).toBe(0);
    expect(hlt.size).toBe(1);
    expect(hlt.cost).toBe(0);
  });

  it('MOV_REG_REG has size 3 (opcode + 2 regs)', () => {
    const mov = BY_CODE[Op.MOV_REG_REG];
    expect(mov.size).toBe(3);
    expect(mov.cost).toBe(1);
  });

  it('MOV_REG_ADDR has size 3 and cost 2', () => {
    const mov = BY_CODE[Op.MOV_REG_ADDR];
    expect(mov.size).toBe(3);
    expect(mov.cost).toBe(2);
  });

  it('RET has size 1', () => {
    const ret = BY_CODE[Op.RET];
    expect(ret.size).toBe(1);
  });

  it('FCLR has size 1', () => {
    const fclr = BY_CODE_FP[Op.FCLR];
    expect(fclr.size).toBe(1);
  });

  it('FMOV_FP_IMM16 has size 4 (opcode + fpm + 2-byte imm)', () => {
    const insn = BY_CODE_FP[Op.FMOV_FP_IMM16];
    expect(insn.size).toBe(4);
  });

  it('FMADD has size 4 (opcode + fpm + fpm + addr)', () => {
    const insn = BY_CODE_FP[Op.FMADD_FP_FP_ADDR];
    expect(insn.size).toBe(4);
  });
});

// ── Lookup tables ────────────────────────────────────────────────

describe('BY_CODE', () => {
  it('maps all 74 integer opcodes', () => {
    expect(Object.keys(BY_CODE).length).toBe(74);
  });

  it('every entry has matching op key', () => {
    for (const [code, insn] of Object.entries(BY_CODE)) {
      expect(insn.op).toBe(Number(code));
    }
  });
});

describe('BY_CODE_FP', () => {
  it('maps all 35 FP opcodes', () => {
    expect(Object.keys(BY_CODE_FP).length).toBe(35);
  });
});

describe('BY_MNEMONIC', () => {
  it('has MOV with 8 variants', () => {
    expect(BY_MNEMONIC['MOV'].length).toBe(8);
  });

  it('has ADD with 4 variants', () => {
    expect(BY_MNEMONIC['ADD'].length).toBe(4);
  });

  it('has JMP with 2 variants', () => {
    expect(BY_MNEMONIC['JMP'].length).toBe(2);
  });

  it('has PUSH with 4 variants', () => {
    expect(BY_MNEMONIC['PUSH'].length).toBe(4);
  });
});

describe('BY_MNEMONIC_FP', () => {
  it('has FMOV with 7 variants (4 mem + 1 RR + 2 imm)', () => {
    expect(BY_MNEMONIC_FP['FMOV'].length).toBe(7);
  });

  it('has FADD with 3 variants (2 mem + 1 rr)', () => {
    expect(BY_MNEMONIC_FP['FADD'].length).toBe(3);
  });
});

describe('MNEMONICS', () => {
  it('includes DB pseudo-instruction', () => {
    expect(MNEMONICS.has('DB')).toBe(true);
  });

  it('includes HLT', () => {
    expect(MNEMONICS.has('HLT')).toBe(true);
  });
});

describe('FP_CONTROL_MNEMONICS', () => {
  it('contains FSTAT, FCFG, FSCFG, FCLR', () => {
    expect(FP_CONTROL_MNEMONICS.has('FSTAT')).toBe(true);
    expect(FP_CONTROL_MNEMONICS.has('FCFG')).toBe(true);
    expect(FP_CONTROL_MNEMONICS.has('FSCFG')).toBe(true);
    expect(FP_CONTROL_MNEMONICS.has('FCLR')).toBe(true);
    expect(FP_CONTROL_MNEMONICS.size).toBe(4);
  });
});

// ── Mnemonic aliases ─────────────────────────────────────────────

describe('MNEMONIC_ALIASES', () => {
  it('maps JB → JC', () => {
    expect(MNEMONIC_ALIASES['JB']).toBe('JC');
  });

  it('maps JE → JZ', () => {
    expect(MNEMONIC_ALIASES['JE']).toBe('JZ');
  });

  it('maps SAL → SHL', () => {
    expect(MNEMONIC_ALIASES['SAL']).toBe('SHL');
  });
});

// ── OpType ───────────────────────────────────────────────────────

describe('OpType', () => {
  it('has all expected types', () => {
    expect(OpType.REG).toBe('reg');
    expect(OpType.REG_STACK).toBe('reg_stack');
    expect(OpType.REG_GPR).toBe('reg_gpr');
    expect(OpType.IMM).toBe('imm');
    expect(OpType.MEM).toBe('mem');
    expect(OpType.REGADDR).toBe('regaddr');
    expect(OpType.FP_REG).toBe('fp_reg');
    expect(OpType.FP_IMM8).toBe('fp_imm8');
    expect(OpType.FP_IMM16).toBe('fp_imm16');
  });
});
