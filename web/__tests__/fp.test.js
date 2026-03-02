import { describe, it, expect } from 'vitest';
import {
  RoundingMode,
  encodeFloat32, decodeFloat32,
  encodeFloat16, decodeFloat16,
  encodeBfloat16, decodeBfloat16,
  encodeOfp8E4M3, decodeOfp8E4M3,
  encodeOfp8E5M2, decodeOfp8E5M2,
  floatToBytes, bytesToFloat,
  fpAdd, fpSub, fpMul, fpDiv, fpSqrt,
  fpCmp, fpAbs, fpNeg, fpClassify,
} from '../lib/fp.js';
import {
  FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2,
} from '../lib/isa.js';

// ── Helpers ────────────────────────────────────────────────────────

function noExc() {
  return { invalid: false, divZero: false, overflow: false, underflow: false, inexact: false };
}

function bytesEqual(actual, expected) {
  expect(actual.length).toBe(expected.length);
  for (let i = 0; i < expected.length; i++) {
    expect(actual[i]).toBe(expected[i]);
  }
}

// ── 1. Float32 encode/decode ────────────────────────────────────────

describe('float32 encode/decode', () => {
  it('encodes 1.0', () => {
    const { data, exc } = encodeFloat32(1.0);
    // 1.0 in float32 LE: 0x3F800000 -> [0x00, 0x00, 0x80, 0x3F]
    bytesEqual(data, [0x00, 0x00, 0x80, 0x3F]);
    expect(exc.inexact).toBe(false);
  });

  it('encodes -1.0', () => {
    const { data } = encodeFloat32(-1.0);
    // -1.0 in float32 LE: 0xBF800000 -> [0x00, 0x00, 0x80, 0xBF]
    bytesEqual(data, [0x00, 0x00, 0x80, 0xBF]);
  });

  it('encodes 3.14 with inexact flag', () => {
    const { data, exc } = encodeFloat32(3.14);
    // 3.14 is not exactly representable in float32
    const rt = decodeFloat32(data);
    expect(Math.abs(rt - 3.14)).toBeLessThan(1e-6);
    expect(exc.inexact).toBe(true);
  });

  it('decodes 1.0', () => {
    const result = decodeFloat32(new Uint8Array([0x00, 0x00, 0x80, 0x3F]));
    expect(result).toBe(1.0);
  });

  it('decodes -1.0', () => {
    const result = decodeFloat32(new Uint8Array([0x00, 0x00, 0x80, 0xBF]));
    expect(result).toBe(-1.0);
  });

  it('encodes and decodes +0', () => {
    const { data, exc } = encodeFloat32(0.0);
    bytesEqual(data, [0x00, 0x00, 0x00, 0x00]);
    expect(decodeFloat32(data)).toBe(0.0);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes -0', () => {
    const { data, exc } = encodeFloat32(-0.0);
    bytesEqual(data, [0x00, 0x00, 0x00, 0x80]);
    expect(Object.is(decodeFloat32(data), -0)).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes +Infinity', () => {
    const { data, exc } = encodeFloat32(Infinity);
    bytesEqual(data, [0x00, 0x00, 0x80, 0x7F]);
    expect(decodeFloat32(data)).toBe(Infinity);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes -Infinity', () => {
    const { data, exc } = encodeFloat32(-Infinity);
    bytesEqual(data, [0x00, 0x00, 0x80, 0xFF]);
    expect(decodeFloat32(data)).toBe(-Infinity);
    expect(exc).toEqual(noExc());
  });

  it('encodes NaN', () => {
    const { data, exc } = encodeFloat32(NaN);
    const rt = decodeFloat32(data);
    expect(Number.isNaN(rt)).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('encodes subnormal with underflow flag', () => {
    // Smallest positive float32 subnormal: 2^-149
    const tiny = 1.4e-45;
    const { data, exc } = encodeFloat32(tiny);
    const rt = decodeFloat32(data);
    expect(rt).toBeGreaterThan(0);
    expect(exc.underflow).toBe(true);
  });

  it('roundtrips normal values', () => {
    for (const v of [0.5, 2.0, 100.0, -42.0, 1e10, -1e-10]) {
      const { data } = encodeFloat32(v);
      const rt = decodeFloat32(data);
      // float32 roundtrip: rt should be the nearest f32 value
      const { data: data2 } = encodeFloat32(rt);
      bytesEqual(data, data2);
    }
  });
});

// ── 2. Float16 encode/decode ────────────────────────────────────────

describe('float16 encode/decode', () => {
  it('encodes 1.0', () => {
    const { data, exc } = encodeFloat16(1.0);
    // 1.0 in float16 LE: 0x3C00 -> [0x00, 0x3C]
    bytesEqual(data, [0x00, 0x3C]);
    expect(exc.inexact).toBe(false);
  });

  it('encodes -1.0', () => {
    const { data } = encodeFloat16(-1.0);
    bytesEqual(data, [0x00, 0xBC]);
  });

  it('decodes 1.0', () => {
    const result = decodeFloat16(new Uint8Array([0x00, 0x3C]));
    expect(result).toBe(1.0);
  });

  it('encodes and decodes +0', () => {
    const { data, exc } = encodeFloat16(0.0);
    bytesEqual(data, [0x00, 0x00]);
    expect(decodeFloat16(data)).toBe(0.0);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes -0', () => {
    const { data, exc } = encodeFloat16(-0.0);
    bytesEqual(data, [0x00, 0x80]);
    expect(Object.is(decodeFloat16(data), -0)).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes +Inf', () => {
    const { data, exc } = encodeFloat16(Infinity);
    // +Inf in float16 LE: 0x7C00 -> [0x00, 0x7C]
    bytesEqual(data, [0x00, 0x7C]);
    expect(decodeFloat16(data)).toBe(Infinity);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes -Inf', () => {
    const { data, exc } = encodeFloat16(-Infinity);
    bytesEqual(data, [0x00, 0xFC]);
    expect(decodeFloat16(data)).toBe(-Infinity);
    expect(exc).toEqual(noExc());
  });

  it('encodes NaN', () => {
    const { data, exc } = encodeFloat16(NaN);
    expect(Number.isNaN(decodeFloat16(data))).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('encodes subnormal with underflow', () => {
    // Smallest positive float16 subnormal: 2^-24 = ~5.96e-8
    const tiny = 5.960464477539063e-8;
    const { data, exc } = encodeFloat16(tiny);
    const rt = decodeFloat16(data);
    expect(rt).toBeGreaterThan(0);
    expect(exc.underflow).toBe(true);
  });

  it('overflow above max produces Inf', () => {
    // float16 max = 65504; values >= 65520 overflow under RNE
    const { data, exc } = encodeFloat16(65520);
    const rt = decodeFloat16(data);
    expect(rt).toBe(Infinity);
    expect(exc.overflow).toBe(true);
    expect(exc.inexact).toBe(true);
  });

  it('encodes 0.5 exactly', () => {
    const { data, exc } = encodeFloat16(0.5);
    bytesEqual(data, [0x00, 0x38]);
    expect(exc.inexact).toBe(false);
  });
});

// ── 3. Bfloat16 encode/decode ──────────────────────────────────────

describe('bfloat16 encode/decode', () => {
  it('encodes 1.0', () => {
    const { data, exc } = encodeBfloat16(1.0);
    // 1.0 in bf16 LE: top 16 bits of float32 0x3F800000 = 0x3F80 -> [0x80, 0x3F]
    bytesEqual(data, [0x80, 0x3F]);
    expect(exc.inexact).toBe(false);
  });

  it('encodes -1.0', () => {
    const { data } = encodeBfloat16(-1.0);
    bytesEqual(data, [0x80, 0xBF]);
  });

  it('decodes 1.0', () => {
    const result = decodeBfloat16(new Uint8Array([0x80, 0x3F]));
    expect(result).toBe(1.0);
  });

  it('encodes and decodes +0', () => {
    const { data, exc } = encodeBfloat16(0.0);
    bytesEqual(data, [0x00, 0x00]);
    expect(decodeBfloat16(data)).toBe(0.0);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes -0', () => {
    const { data, exc } = encodeBfloat16(-0.0);
    bytesEqual(data, [0x00, 0x80]);
    expect(Object.is(decodeBfloat16(data), -0)).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes +Inf', () => {
    const { data, exc } = encodeBfloat16(Infinity);
    // +Inf bf16 LE: 0x7F80 -> [0x80, 0x7F]
    bytesEqual(data, [0x80, 0x7F]);
    expect(decodeBfloat16(data)).toBe(Infinity);
    expect(exc).toEqual(noExc());
  });

  it('encodes and decodes -Inf', () => {
    const { data, exc } = encodeBfloat16(-Infinity);
    bytesEqual(data, [0x80, 0xFF]);
    expect(decodeBfloat16(data)).toBe(-Infinity);
    expect(exc).toEqual(noExc());
  });

  it('encodes NaN as canonical 0x7FC0', () => {
    const { data, exc } = encodeBfloat16(NaN);
    bytesEqual(data, [0xC0, 0x7F]);
    expect(Number.isNaN(decodeBfloat16(data))).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('encodes 3.14 with inexact flag', () => {
    const { data, exc } = encodeBfloat16(3.14);
    expect(exc.inexact).toBe(true);
    const rt = decodeBfloat16(data);
    expect(Math.abs(rt - 3.14)).toBeLessThan(0.1);
  });
});

// ── 4. OFP8 E4M3 ──────────────────────────────────────────────────

describe('OFP8 E4M3', () => {
  it('encodes 1.0', () => {
    const { data, exc } = encodeOfp8E4M3(1.0);
    // E4M3: exp=7(=bias), mant=0 -> 0b0_0111_000 = 0x38
    expect(data[0]).toBe(0x38);
    expect(exc.inexact).toBe(false);
  });

  it('decodes 1.0', () => {
    expect(decodeOfp8E4M3(0x38)).toBe(1.0);
  });

  it('encodes max finite 448.0', () => {
    const { data } = encodeOfp8E4M3(448.0);
    // max: exp=15, mant=110 -> 0b0_1111_110 = 0x7E
    expect(data[0]).toBe(0x7E);
  });

  it('decodes max finite 0x7E = 448.0', () => {
    expect(decodeOfp8E4M3(0x7E)).toBe(448.0);
  });

  it('has no Inf -- saturates to max on Inf input', () => {
    const { data, exc } = encodeOfp8E4M3(Infinity);
    expect(data[0]).toBe(0x7E);
    expect(exc.overflow).toBe(true);
    expect(exc.inexact).toBe(true);
  });

  it('saturates -Inf to -max (0xFE)', () => {
    const { data, exc } = encodeOfp8E4M3(-Infinity);
    expect(data[0]).toBe(0xFE);
    expect(exc.overflow).toBe(true);
    expect(decodeOfp8E4M3(0xFE)).toBe(-448.0);
  });

  it('NaN encodes to 0x7F', () => {
    const { data, exc } = encodeOfp8E4M3(NaN);
    expect(data[0]).toBe(0x7F);
    expect(exc.invalid).toBe(true);
  });

  it('decodes 0x7F as NaN', () => {
    expect(Number.isNaN(decodeOfp8E4M3(0x7F))).toBe(true);
  });

  it('encodes +0', () => {
    const { data, exc } = encodeOfp8E4M3(0.0);
    expect(data[0]).toBe(0x00);
    expect(exc).toEqual(noExc());
  });

  it('encodes -0', () => {
    const { data, exc } = encodeOfp8E4M3(-0.0);
    expect(data[0]).toBe(0x80);
    expect(exc).toEqual(noExc());
  });

  it('decodes +0', () => {
    expect(decodeOfp8E4M3(0x00)).toBe(0.0);
    expect(Object.is(decodeOfp8E4M3(0x00), -0)).toBe(false);
  });

  it('decodes -0', () => {
    expect(Object.is(decodeOfp8E4M3(0x80), -0)).toBe(true);
  });

  it('overflow above 448 saturates', () => {
    const { data, exc } = encodeOfp8E4M3(500.0);
    expect(data[0]).toBe(0x7E);
    expect(exc.overflow).toBe(true);
  });

  it('smallest subnormal (2^-9) roundtrips', () => {
    const smallest = Math.pow(2, -9);
    const { data } = encodeOfp8E4M3(smallest);
    expect(data[0]).toBe(0x01);
    expect(decodeOfp8E4M3(0x01)).toBe(smallest);
  });

  it('encodes 2.0', () => {
    const { data } = encodeOfp8E4M3(2.0);
    // 2.0 = 1.0 * 2^1 -> biased_exp = 1+7 = 8, mant=0 -> 0b0_1000_000 = 0x40
    expect(data[0]).toBe(0x40);
  });

  it('encodes -1.0', () => {
    const { data } = encodeOfp8E4M3(-1.0);
    // sign=1, exp=7, mant=0 -> 0b1_0111_000 = 0xB8
    expect(data[0]).toBe(0xB8);
  });
});

// ── 5. OFP8 E5M2 ──────────────────────────────────────────────────

describe('OFP8 E5M2', () => {
  it('encodes 1.0', () => {
    const { data, exc } = encodeOfp8E5M2(1.0);
    // E5M2: exp=15(=bias), mant=0 -> 0b0_01111_00 = 0x3C
    expect(data[0]).toBe(0x3C);
    expect(exc.inexact).toBe(false);
  });

  it('decodes 1.0', () => {
    expect(decodeOfp8E5M2(0x3C)).toBe(1.0);
  });

  it('max finite is 57344.0', () => {
    const { data } = encodeOfp8E5M2(57344.0);
    // max: exp=30, mant=11 -> 0b0_11110_11 = 0x7B
    expect(data[0]).toBe(0x7B);
    expect(decodeOfp8E5M2(0x7B)).toBe(57344.0);
  });

  it('encodes +Inf', () => {
    const { data, exc } = encodeOfp8E5M2(Infinity);
    // +Inf: exp=31, mant=00 -> 0b0_11111_00 = 0x7C
    expect(data[0]).toBe(0x7C);
    expect(exc).toEqual(noExc());
  });

  it('decodes 0x7C as +Inf', () => {
    expect(decodeOfp8E5M2(0x7C)).toBe(Infinity);
  });

  it('encodes -Inf', () => {
    const { data, exc } = encodeOfp8E5M2(-Infinity);
    expect(data[0]).toBe(0xFC);
    expect(exc).toEqual(noExc());
    expect(decodeOfp8E5M2(0xFC)).toBe(-Infinity);
  });

  it('NaN encodes to 0x7D (canonical qNaN)', () => {
    const { data, exc } = encodeOfp8E5M2(NaN);
    expect(data[0]).toBe(0x7D);
    expect(exc.invalid).toBe(true);
  });

  it('decodes 0x7D as NaN', () => {
    expect(Number.isNaN(decodeOfp8E5M2(0x7D))).toBe(true);
  });

  it('decodes 0x7E as NaN (exp=31, mant=10)', () => {
    expect(Number.isNaN(decodeOfp8E5M2(0x7E))).toBe(true);
  });

  it('decodes 0x7F as NaN (exp=31, mant=11)', () => {
    expect(Number.isNaN(decodeOfp8E5M2(0x7F))).toBe(true);
  });

  it('encodes +0', () => {
    const { data } = encodeOfp8E5M2(0.0);
    expect(data[0]).toBe(0x00);
  });

  it('encodes -0', () => {
    const { data } = encodeOfp8E5M2(-0.0);
    expect(data[0]).toBe(0x80);
  });

  it('decodes +0 and -0', () => {
    expect(decodeOfp8E5M2(0x00)).toBe(0.0);
    expect(Object.is(decodeOfp8E5M2(0x80), -0)).toBe(true);
  });

  it('overflow above max to Inf', () => {
    const { data, exc } = encodeOfp8E5M2(65536.0);
    expect(decodeOfp8E5M2(data[0])).toBe(Infinity);
    expect(exc.overflow).toBe(true);
  });

  it('smallest subnormal (2^-16) roundtrips', () => {
    const smallest = Math.pow(2, -16);
    const { data } = encodeOfp8E5M2(smallest);
    expect(data[0]).toBe(0x01);
    expect(decodeOfp8E5M2(0x01)).toBe(smallest);
  });

  it('encodes 1.5', () => {
    const { data } = encodeOfp8E5M2(1.5);
    // 1.5 = 1.11 * 2^0 -> exp=15, mant=11 -> 0b0_01111_10 = 0x3E
    expect(data[0]).toBe(0x3E);
  });
});

// ── 6. Rounding modes ──────────────────────────────────────────────

describe('rounding modes', () => {
  it('exports correct constants', () => {
    expect(RoundingMode.RNE).toBe(0);
    expect(RoundingMode.RTZ).toBe(1);
    expect(RoundingMode.RDN).toBe(2);
    expect(RoundingMode.RUP).toBe(3);
  });

  // f16 values near 1.001: 0x3C01 = 1.0009765625, 0x3C02 = 1.001953125
  // 1.001 sits between these two, much closer to 1.0009765625
  // Distance to 1.0009765625: ~0.0000234, distance to 1.001953125: ~0.000953
  it('RNE rounds 1.001 to nearest in float16', () => {
    const { data } = encodeFloat16(1.001, RoundingMode.RNE);
    const rt = decodeFloat16(data);
    expect(rt).toBe(1.0009765625); // nearest
  });

  it('RTZ truncates 1.001 toward zero in float16', () => {
    const { data } = encodeFloat16(1.001, RoundingMode.RTZ);
    const rt = decodeFloat16(data);
    expect(rt).toBe(1.0009765625); // truncate toward zero = lower magnitude
  });

  it('RDN rounds 1.001 toward -Inf in float16 (same as truncate for positive)', () => {
    const { data } = encodeFloat16(1.001, RoundingMode.RDN);
    const rt = decodeFloat16(data);
    expect(rt).toBe(1.0009765625); // floor for positive
  });

  it('RUP rounds 1.001 toward +Inf in float16', () => {
    const { data } = encodeFloat16(1.001, RoundingMode.RUP);
    const rt = decodeFloat16(data);
    // RUP: positive value rounds up to next representable
    expect(rt).toBe(1.001953125);
  });

  // Negative value: -1.001 -- between -1.001953125 and -1.0009765625
  // RDN should round toward -Inf (more negative = -1.001953125)
  it('RDN rounds -1.001 toward -Inf in float16 (away from zero)', () => {
    const { data } = encodeFloat16(-1.001, RoundingMode.RDN);
    const rt = decodeFloat16(data);
    expect(rt).toBe(-1.001953125); // floor = more negative
  });

  it('RUP rounds -1.001 toward +Inf in float16 (toward zero)', () => {
    const { data } = encodeFloat16(-1.001, RoundingMode.RUP);
    const rt = decodeFloat16(data);
    expect(rt).toBe(-1.0009765625); // ceil for negative = toward zero
  });

  // E5M2 rounding: near overflow boundary
  it('RTZ near E5M2 overflow stays at max', () => {
    const { data } = encodeOfp8E5M2(60000.0, RoundingMode.RTZ);
    expect(data[0]).toBe(0x7B); // MAX = 57344
  });

  it('RUP positive near E5M2 max overflows to Inf', () => {
    const { data, exc } = encodeOfp8E5M2(57345.0, RoundingMode.RUP);
    expect(data[0]).toBe(0x7C); // +Inf
    expect(exc.overflow).toBe(true);
  });
});

// ── 7. FP arithmetic ───────────────────────────────────────────────

describe('fpAdd', () => {
  it('adds normal values', () => {
    const { result, exc } = fpAdd(1.0, 2.0, FP_FMT_F);
    expect(result).toBe(3.0);
    expect(exc.inexact).toBe(false);
  });

  it('NaN propagates', () => {
    const { result, exc } = fpAdd(NaN, 1.0, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('NaN + NaN = NaN', () => {
    const { result, exc } = fpAdd(NaN, NaN, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf + (-Inf) = NaN (invalid)', () => {
    const { result, exc } = fpAdd(Infinity, -Infinity, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf + Inf = Inf', () => {
    const { result } = fpAdd(Infinity, Infinity, FP_FMT_F);
    expect(result).toBe(Infinity);
  });

  it('0 + 0 = 0', () => {
    const { result } = fpAdd(0.0, 0.0, FP_FMT_F);
    expect(result).toBe(0.0);
  });
});

describe('fpSub', () => {
  it('subtracts normal values', () => {
    const { result } = fpSub(5.0, 3.0, FP_FMT_F);
    expect(result).toBe(2.0);
  });

  it('NaN propagates', () => {
    const { result, exc } = fpSub(1.0, NaN, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf - Inf = NaN (invalid)', () => {
    const { result, exc } = fpSub(Infinity, Infinity, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf - (-Inf) = Inf', () => {
    const { result } = fpSub(Infinity, -Infinity, FP_FMT_F);
    expect(result).toBe(Infinity);
  });
});

describe('fpMul', () => {
  it('multiplies normal values', () => {
    const { result } = fpMul(3.0, 4.0, FP_FMT_F);
    expect(result).toBe(12.0);
  });

  it('0 * Inf = NaN (invalid)', () => {
    const { result, exc } = fpMul(0.0, Infinity, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf * 0 = NaN (invalid)', () => {
    const { result, exc } = fpMul(Infinity, 0.0, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('NaN propagates', () => {
    const { result, exc } = fpMul(NaN, 5.0, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf * finite = Inf', () => {
    const { result } = fpMul(Infinity, 2.0, FP_FMT_F);
    expect(result).toBe(Infinity);
  });

  it('negative * negative = positive', () => {
    const { result } = fpMul(-3.0, -4.0, FP_FMT_F);
    expect(result).toBe(12.0);
  });
});

describe('fpDiv', () => {
  it('divides normal values', () => {
    const { result } = fpDiv(10.0, 2.0, FP_FMT_F);
    expect(result).toBe(5.0);
  });

  it('finite / 0 = Inf (div_zero)', () => {
    const { result, exc } = fpDiv(1.0, 0.0, FP_FMT_F);
    expect(result).toBe(Infinity);
    expect(exc.divZero).toBe(true);
  });

  it('negative / 0 = -Inf', () => {
    const { result, exc } = fpDiv(-1.0, 0.0, FP_FMT_F);
    expect(result).toBe(-Infinity);
    expect(exc.divZero).toBe(true);
  });

  it('0 / 0 = NaN (invalid)', () => {
    const { result, exc } = fpDiv(0.0, 0.0, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf / Inf = NaN (invalid)', () => {
    const { result, exc } = fpDiv(Infinity, Infinity, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('NaN propagates', () => {
    const { result, exc } = fpDiv(NaN, 1.0, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf / finite = Inf', () => {
    const { result } = fpDiv(Infinity, 2.0, FP_FMT_F);
    expect(result).toBe(Infinity);
  });

  it('finite / Inf = 0', () => {
    const { result } = fpDiv(1.0, Infinity, FP_FMT_F);
    expect(result).toBe(0.0);
  });

  it('sign of div by -0: positive / -0 = -Inf', () => {
    const { result, exc } = fpDiv(1.0, -0.0, FP_FMT_F);
    expect(result).toBe(-Infinity);
    expect(exc.divZero).toBe(true);
  });
});

// ── 8. fpCmp ──────────────────────────────────────────────────────

describe('fpCmp', () => {
  it('equal values: zero=true, carry=false', () => {
    const { zero, carry, exc } = fpCmp(1.0, 1.0);
    expect(zero).toBe(true);
    expect(carry).toBe(false);
    expect(exc).toEqual(noExc());
  });

  it('+0 == -0', () => {
    const { zero, carry } = fpCmp(0.0, -0.0);
    expect(zero).toBe(true);
    expect(carry).toBe(false);
  });

  it('less than: zero=false, carry=true', () => {
    const { zero, carry, exc } = fpCmp(1.0, 2.0);
    expect(zero).toBe(false);
    expect(carry).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('greater than: zero=false, carry=false', () => {
    const { zero, carry, exc } = fpCmp(3.0, 1.0);
    expect(zero).toBe(false);
    expect(carry).toBe(false);
    expect(exc).toEqual(noExc());
  });

  it('unordered (NaN): zero=true, carry=true, invalid', () => {
    const { zero, carry, exc } = fpCmp(NaN, 1.0);
    expect(zero).toBe(true);
    expect(carry).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('both NaN: unordered', () => {
    const { zero, carry, exc } = fpCmp(NaN, NaN);
    expect(zero).toBe(true);
    expect(carry).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('Inf == Inf', () => {
    const { zero, carry } = fpCmp(Infinity, Infinity);
    expect(zero).toBe(true);
    expect(carry).toBe(false);
  });

  it('-Inf < Inf', () => {
    const { zero, carry } = fpCmp(-Infinity, Infinity);
    expect(zero).toBe(false);
    expect(carry).toBe(true);
  });
});

// ── 9. fpSqrt ─────────────────────────────────────────────────────

describe('fpSqrt', () => {
  it('sqrt(4) = 2', () => {
    const { result, exc } = fpSqrt(4.0, FP_FMT_F);
    expect(result).toBe(2.0);
    expect(exc.inexact).toBe(false);
  });

  it('sqrt(0) = 0', () => {
    const { result, exc } = fpSqrt(0.0, FP_FMT_F);
    expect(result).toBe(0.0);
    expect(exc).toEqual(noExc());
  });

  it('sqrt(-0) = -0', () => {
    const { result, exc } = fpSqrt(-0.0, FP_FMT_F);
    expect(Object.is(result, -0)).toBe(true);
    expect(exc).toEqual(noExc());
  });

  it('sqrt(negative) = NaN (invalid)', () => {
    const { result, exc } = fpSqrt(-1.0, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('sqrt(NaN) = NaN (invalid)', () => {
    const { result, exc } = fpSqrt(NaN, FP_FMT_F);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });

  it('sqrt(Inf) = Inf', () => {
    const { result, exc } = fpSqrt(Infinity, FP_FMT_F);
    expect(result).toBe(Infinity);
    expect(exc).toEqual(noExc());
  });

  it('sqrt(2) is inexact', () => {
    const { result, exc } = fpSqrt(2.0, FP_FMT_F);
    expect(Math.abs(result - Math.SQRT2)).toBeLessThan(1e-6);
    expect(exc.inexact).toBe(true);
  });

  it('sqrt(1) = 1', () => {
    const { result } = fpSqrt(1.0, FP_FMT_F);
    expect(result).toBe(1.0);
  });
});

// ── 10. fpAbs ──────────────────────────────────────────────────────

describe('fpAbs', () => {
  it('clears sign bit of 8-bit value', () => {
    // -1.0 in E4M3: 0xB8, abs -> 0x38 (1.0)
    expect(fpAbs(0xB8, 8)).toBe(0x38);
  });

  it('preserves positive value', () => {
    expect(fpAbs(0x38, 8)).toBe(0x38);
  });

  it('clears sign bit of 16-bit value', () => {
    // -1.0 in float16: 0xBC00, abs -> 0x3C00
    expect(fpAbs(0xBC00, 16)).toBe(0x3C00);
  });

  it('clears sign bit of 32-bit value', () => {
    // -1.0 in float32: 0xBF800000, abs -> 0x3F800000
    expect(fpAbs(0xBF800000, 32)).toBe(0x3F800000);
  });

  it('abs of +0 stays +0', () => {
    expect(fpAbs(0x00, 8)).toBe(0x00);
  });

  it('abs of -0 gives +0', () => {
    // -0 in E4M3: 0x80
    expect(fpAbs(0x80, 8)).toBe(0x00);
  });

  it('abs of NaN keeps magnitude bits', () => {
    // NaN in E4M3 is 0x7F; sign=0 already
    expect(fpAbs(0x7F, 8)).toBe(0x7F);
  });
});

// ── 11. fpNeg ──────────────────────────────────────────────────────

describe('fpNeg', () => {
  it('toggles sign bit of 8-bit value (positive to negative)', () => {
    // 1.0 in E4M3: 0x38, neg -> 0xB8 (-1.0)
    expect(fpNeg(0x38, 8)).toBe(0xB8);
  });

  it('toggles sign bit of 8-bit value (negative to positive)', () => {
    expect(fpNeg(0xB8, 8)).toBe(0x38);
  });

  it('toggles sign bit of 16-bit value', () => {
    expect(fpNeg(0x3C00, 16)).toBe(0xBC00);
  });

  it('toggles sign bit of 32-bit value', () => {
    expect(fpNeg(0x3F800000, 32)).toBe(0xBF800000);
  });

  it('neg of +0 gives -0', () => {
    expect(fpNeg(0x00, 8)).toBe(0x80);
  });

  it('neg of -0 gives +0', () => {
    expect(fpNeg(0x80, 8)).toBe(0x00);
  });

  it('double negation is identity', () => {
    expect(fpNeg(fpNeg(0x38, 8), 8)).toBe(0x38);
  });
});

// ── 12. fpClassify ─────────────────────────────────────────────────

describe('fpClassify', () => {
  // Bit layout: bit0=ZERO, bit1=SUB, bit2=NORM, bit3=INF, bit4=QNAN, bit6=NEG

  it('classifies +0 as ZERO', () => {
    const result = fpClassify(0.0, 0x00, 8, FP_FMT_O3);
    expect(result & 0x01).toBe(0x01); // ZERO
    expect(result & 0x40).toBe(0x00); // not NEG
  });

  it('classifies -0 as ZERO + NEG', () => {
    const result = fpClassify(-0.0, 0x80, 8, FP_FMT_O3);
    expect(result & 0x01).toBe(0x01); // ZERO
    expect(result & 0x40).toBe(0x40); // NEG
  });

  it('classifies positive normal as NORM', () => {
    // 1.0 in E4M3: 0x38
    const result = fpClassify(1.0, 0x38, 8, FP_FMT_O3);
    expect(result & 0x04).toBe(0x04); // NORM
    expect(result & 0x40).toBe(0x00); // not NEG
  });

  it('classifies negative normal as NORM + NEG', () => {
    // -1.0 in E4M3: 0xB8
    const result = fpClassify(-1.0, 0xB8, 8, FP_FMT_O3);
    expect(result & 0x04).toBe(0x04); // NORM
    expect(result & 0x40).toBe(0x40); // NEG
  });

  it('classifies subnormal as SUB', () => {
    // Smallest E4M3 subnormal: 0x01 (exp=0, mant=001)
    const val = decodeOfp8E4M3(0x01);
    const result = fpClassify(val, 0x01, 8, FP_FMT_O3);
    expect(result & 0x02).toBe(0x02); // SUB
    expect(result & 0x40).toBe(0x00); // not NEG
  });

  it('classifies negative subnormal as SUB + NEG', () => {
    // Negative E4M3 subnormal: 0x81
    const val = decodeOfp8E4M3(0x81);
    const result = fpClassify(val, 0x81, 8, FP_FMT_O3);
    expect(result & 0x02).toBe(0x02); // SUB
    expect(result & 0x40).toBe(0x40); // NEG
  });

  it('classifies +Inf as INF (E5M2)', () => {
    const result = fpClassify(Infinity, 0x7C, 8, FP_FMT_O2);
    expect(result & 0x08).toBe(0x08); // INF
    expect(result & 0x40).toBe(0x00); // not NEG
  });

  it('classifies -Inf as INF + NEG (E5M2)', () => {
    const result = fpClassify(-Infinity, 0xFC, 8, FP_FMT_O2);
    expect(result & 0x08).toBe(0x08); // INF
    expect(result & 0x40).toBe(0x40); // NEG
  });

  it('classifies NaN as QNAN', () => {
    const result = fpClassify(NaN, 0x7F, 8, FP_FMT_O3);
    expect(result & 0x10).toBe(0x10); // QNAN
  });

  it('classifies float32 normal', () => {
    // 1.0 in float32: 0x3F800000
    const result = fpClassify(1.0, 0x3F800000, 32, FP_FMT_F);
    expect(result & 0x04).toBe(0x04); // NORM
    expect(result & 0x40).toBe(0x00); // not NEG
  });

  it('classifies float16 positive normal', () => {
    // 1.0 in float16: 0x3C00
    const result = fpClassify(1.0, 0x3C00, 16, FP_FMT_H);
    expect(result & 0x04).toBe(0x04); // NORM
  });

  it('classifies bfloat16 zero', () => {
    const result = fpClassify(0.0, 0x0000, 16, FP_FMT_BF);
    expect(result & 0x01).toBe(0x01); // ZERO
  });

  it('class bits are mutually exclusive (zero vs norm vs sub vs inf vs nan)', () => {
    // Test several values: the lower 5 bits should have exactly one set
    const testCases = [
      { value: 0.0, bits: 0x00, width: 8, fmt: FP_FMT_O3 },
      { value: 1.0, bits: 0x38, width: 8, fmt: FP_FMT_O3 },
      { value: NaN, bits: 0x7F, width: 8, fmt: FP_FMT_O3 },
      { value: Infinity, bits: 0x7C, width: 8, fmt: FP_FMT_O2 },
    ];
    for (const { value, bits, width, fmt } of testCases) {
      const result = fpClassify(value, bits, width, fmt);
      const classBits = result & 0x1F; // bits 0-4
      // Exactly one class bit should be set
      expect(classBits).toBeGreaterThan(0);
      expect(classBits & (classBits - 1)).toBe(0); // power of 2 check
    }
  });
});

// ── 13. Dispatcher: floatToBytes and bytesToFloat ─────────────────

describe('floatToBytes / bytesToFloat dispatchers', () => {
  it('dispatches float32', () => {
    const { data } = floatToBytes(1.0, FP_FMT_F);
    expect(data.length).toBe(4);
    bytesEqual(data, [0x00, 0x00, 0x80, 0x3F]);
    expect(bytesToFloat(data, FP_FMT_F)).toBe(1.0);
  });

  it('dispatches float16', () => {
    const { data } = floatToBytes(1.0, FP_FMT_H);
    expect(data.length).toBe(2);
    bytesEqual(data, [0x00, 0x3C]);
    expect(bytesToFloat(data, FP_FMT_H)).toBe(1.0);
  });

  it('dispatches bfloat16', () => {
    const { data } = floatToBytes(1.0, FP_FMT_BF);
    expect(data.length).toBe(2);
    bytesEqual(data, [0x80, 0x3F]);
    expect(bytesToFloat(data, FP_FMT_BF)).toBe(1.0);
  });

  it('dispatches OFP8 E4M3', () => {
    const { data } = floatToBytes(1.0, FP_FMT_O3);
    expect(data.length).toBe(1);
    expect(data[0]).toBe(0x38);
    expect(bytesToFloat(data, FP_FMT_O3)).toBe(1.0);
  });

  it('dispatches OFP8 E5M2', () => {
    const { data } = floatToBytes(1.0, FP_FMT_O2);
    expect(data.length).toBe(1);
    expect(data[0]).toBe(0x3C);
    expect(bytesToFloat(data, FP_FMT_O2)).toBe(1.0);
  });

  it('roundtrips NaN through each format', () => {
    for (const fmt of [FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2]) {
      const { data } = floatToBytes(NaN, fmt);
      expect(Number.isNaN(bytesToFloat(data, fmt))).toBe(true);
    }
  });

  it('roundtrips zero through each format', () => {
    for (const fmt of [FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2]) {
      const { data } = floatToBytes(0.0, fmt);
      expect(bytesToFloat(data, fmt)).toBe(0.0);
    }
  });

  it('roundtrips Inf through formats that support it', () => {
    for (const fmt of [FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O2]) {
      const { data } = floatToBytes(Infinity, fmt);
      expect(bytesToFloat(data, fmt)).toBe(Infinity);
    }
  });

  it('E4M3 Inf saturates to max via dispatcher', () => {
    const { data, exc } = floatToBytes(Infinity, FP_FMT_O3);
    expect(bytesToFloat(data, FP_FMT_O3)).toBe(448.0);
    expect(exc.overflow).toBe(true);
  });

  it('passes rounding mode through dispatcher', () => {
    const { data } = floatToBytes(1.001, FP_FMT_H, RoundingMode.RUP);
    const rt = bytesToFloat(data, FP_FMT_H);
    expect(rt).toBe(1.001953125); // RUP rounds up to next representable
  });

  it('roundtrips -0 through each format', () => {
    for (const fmt of [FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2]) {
      const { data } = floatToBytes(-0.0, fmt);
      const rt = bytesToFloat(data, fmt);
      expect(Object.is(rt, -0)).toBe(true);
    }
  });
});

// ── Additional arithmetic edge cases ──────────────────────────────

describe('arithmetic in float16 format', () => {
  it('fpAdd in float16', () => {
    const { result } = fpAdd(1.0, 2.0, FP_FMT_H);
    expect(result).toBe(3.0);
  });

  it('fpMul overflow in float16', () => {
    const { result, exc } = fpMul(60000.0, 2.0, FP_FMT_H);
    expect(result).toBe(Infinity);
    expect(exc.overflow).toBe(true);
  });

  it('fpDiv in float16', () => {
    const { result } = fpDiv(6.0, 3.0, FP_FMT_H);
    expect(result).toBe(2.0);
  });

  it('fpSqrt in float16', () => {
    const { result } = fpSqrt(4.0, FP_FMT_H);
    expect(result).toBe(2.0);
  });
});

describe('arithmetic in E4M3 format', () => {
  it('fpAdd clamps to max on overflow', () => {
    const { result, exc } = fpAdd(448.0, 448.0, FP_FMT_O3);
    // 896 overflows E4M3 max (448), should saturate to max
    expect(result).toBe(448.0);
    expect(exc.overflow).toBe(true);
  });

  it('fpMul 0 * NaN = NaN', () => {
    const { result, exc } = fpMul(0.0, NaN, FP_FMT_O3);
    expect(Number.isNaN(result)).toBe(true);
    expect(exc.invalid).toBe(true);
  });
});
