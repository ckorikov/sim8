/**
 * IEEE 754 floating-point format encode/decode.
 *
 * Supports: float32, float16, bfloat16, OFP8 E4M3, OFP8 E5M2.
 * Port of pysim8/src/pysim8/fp_formats.py to JavaScript ES module.
 * No simulator dependencies -- used by both assembler and simulator.
 */

import {
  FP_FMT_F,
  FP_FMT_H,
  FP_FMT_BF,
  FP_FMT_O3,
  FP_FMT_O2,
} from './isa.js';

// ── Rounding modes ──────────────────────────────────────────────

export const RoundingMode = Object.freeze({
  RNE: 0,  // Round to Nearest, ties to Even
  RTZ: 1,  // Round toward Zero
  RDN: 2,  // Round toward -Inf
  RUP: 3,  // Round toward +Inf
});

// ── Exception flags ─────────────────────────────────────────────

const NO_EXC = Object.freeze({
  invalid: false,
  divZero: false,
  overflow: false,
  underflow: false,
  inexact: false,
});

function exc({ invalid = false, divZero = false, overflow = false,
               underflow = false, inexact = false } = {}) {
  return Object.freeze({ invalid, divZero, overflow, underflow, inexact });
}

function excReplace(base, overrides) {
  return exc({
    invalid: overrides.invalid !== undefined ? overrides.invalid : base.invalid,
    divZero: overrides.divZero !== undefined ? overrides.divZero : base.divZero,
    overflow: overrides.overflow !== undefined ? overrides.overflow : base.overflow,
    underflow: overrides.underflow !== undefined ? overrides.underflow : base.underflow,
    inexact: overrides.inexact !== undefined ? overrides.inexact : base.inexact,
  });
}

// ── Shared typed-array buffers for float32 <-> bits ─────────────

const _f32buf = new ArrayBuffer(4);
const _f32arr = new Float32Array(_f32buf);
const _u32arr = new Uint32Array(_f32buf);

// ── nextafter / copysign helpers ────────────────────────────────

const _f64buf = new ArrayBuffer(8);
const _f64view = new Float64Array(_f64buf);
const _i64view = new BigInt64Array(_f64buf);

function nextafter(from, to) {
  if (Number.isNaN(from) || Number.isNaN(to)) return NaN;
  if (from === to) return to;
  if (from === 0) {
    return to > 0 ? 5e-324 : -5e-324;
  }
  _f64view[0] = from;
  if ((from < to) === (from > 0)) {
    _i64view[0] += 1n;
  } else {
    _i64view[0] -= 1n;
  }
  return _f64view[0];
}

function copysign(x, y) {
  const ax = Math.abs(x);
  return (y < 0 || Object.is(y, -0)) ? -ax : ax;
}

// ── IEEE 754 boundary constants ─────────────────────────────────

const _MIN_NORMAL_F32 = 1.1754943508222875e-38;   // 2^-126
const _MIN_NORMAL_F16 = 6.103515625e-05;           // 2^-14
const _OVERFLOW_THRESH_F32 = 3.4028235677973366e+38;
const _OVERFLOW_THRESH_F16 = 65520.0;

// ── float32 ─────────────────────────────────────────────────────

export function encodeFloat32(value, rm = 0) {
  if (Number.isNaN(value) || !Number.isFinite(value) || value === 0) {
    // Use hardware float32 for NaN, Inf, zero
    _f32arr[0] = value;
    const data = new Uint8Array(4);
    data[0] = _u32arr[0] & 0xFF;
    data[1] = (_u32arr[0] >> 8) & 0xFF;
    data[2] = (_u32arr[0] >> 16) & 0xFF;
    data[3] = (_u32arr[0] >> 24) & 0xFF;
    return { data, exc: NO_EXC };
  }

  if (rm !== RoundingMode.RNE) {
    return _encodeIeeeDirected(value, 8, 23, 127, rm);
  }

  // RNE: use hardware Float32Array for accurate rounding
  if (Math.abs(value) >= _OVERFLOW_THRESH_F32) {
    const sign = value < 0 ? -1.0 : 1.0;
    _f32arr[0] = sign * Infinity;
    const data = new Uint8Array(4);
    data[0] = _u32arr[0] & 0xFF;
    data[1] = (_u32arr[0] >> 8) & 0xFF;
    data[2] = (_u32arr[0] >> 16) & 0xFF;
    data[3] = (_u32arr[0] >> 24) & 0xFF;
    return { data, exc: exc({ overflow: true, inexact: true }) };
  }

  _f32arr[0] = value;
  const f32Bits = _u32arr[0];
  const rt = _f32arr[0];

  const data = new Uint8Array(4);
  data[0] = f32Bits & 0xFF;
  data[1] = (f32Bits >> 8) & 0xFF;
  data[2] = (f32Bits >> 16) & 0xFF;
  data[3] = (f32Bits >> 24) & 0xFF;

  const overflow = !Number.isFinite(rt) && Number.isFinite(value);
  const expBits = (f32Bits >>> 23) & 0xFF;
  const isSub = expBits === 0 && (f32Bits & 0x7FFFFF) !== 0;
  const flushedToZero = rt === 0 && value !== 0;
  const exactSubnormal = 0 < Math.abs(value) && Math.abs(value) < _MIN_NORMAL_F32;
  const underflow = isSub || flushedToZero || exactSubnormal;
  const inexact = rt !== value;

  return {
    data,
    exc: exc({ overflow, underflow, inexact: inexact || overflow }),
  };
}

export function decodeFloat32(data) {
  _u32arr[0] = data[0] | (data[1] << 8) | (data[2] << 16) | ((data[3] << 24) >>> 0);
  return _f32arr[0];
}

// ── float16 ─────────────────────────────────────────────────────

// Manual float16 encode (no DataView.getFloat16 for portability)
function _encodeFloat16Rne(value) {
  // Get float32 bits
  _f32arr[0] = value;
  const f32Bits = _u32arr[0];

  const f32Sign = (f32Bits >>> 31) & 1;
  const f32Exp = (f32Bits >>> 23) & 0xFF;
  const f32Mant = f32Bits & 0x7FFFFF;

  let f16Sign = f32Sign;
  let f16Exp;
  let f16Mant;

  const unbiasedExp = f32Exp - 127;

  if (f32Exp === 0) {
    // f32 subnormal or zero -> f16 zero (too tiny for f16 subnormals)
    f16Exp = 0;
    f16Mant = 0;
  } else if (f32Exp === 0xFF) {
    // Inf or NaN in f32
    f16Exp = 0x1F;
    f16Mant = f32Mant !== 0 ? 0x200 : 0;  // preserve NaN vs Inf
  } else if (unbiasedExp < -24) {
    // Too small: rounds to zero
    f16Exp = 0;
    f16Mant = 0;
  } else if (unbiasedExp < -14) {
    // f16 subnormal range
    f16Exp = 0;
    // Full significand with implicit 1: (1.mant) * 2^(unbiasedExp)
    // f16 subnormals: (0.mant) * 2^(-14)
    // So shift amount = -14 - unbiasedExp + 13 (since f32 has 23 mant bits, f16 has 10)
    const fullMant = (1 << 23) | f32Mant;
    // We want to shift from 23-bit mantissa to 10-bit, plus extra shift for subnormal
    const shiftAmount = -1 - unbiasedExp + 13;  // = 13 - unbiasedExp - 1
    // Actually: denorm shift
    // f16 denorm value = mant/1024 * 2^(-14)
    // = fullMant * 2^(unbiasedExp - 23) but we need mant/1024 * 2^(-14)
    // so mant = fullMant * 2^(unbiasedExp + 14 - 23) = fullMant >> (9 - unbiasedExp - 14)
    // = fullMant >> (23 - 10 - (unbiasedExp + 14))
    // = fullMant >> (23 - 10 - unbiasedExp - 14)
    // = fullMant >> (-1 - unbiasedExp)
    const shift = -1 - unbiasedExp;  // how many bits to shift right from 23-bit
    // We need to keep 10 bits, but after shifting for subnormality
    // Round to nearest even
    const shifted = fullMant >> shift;
    const remainder = fullMant & ((1 << shift) - 1);
    const halfway = 1 << (shift - 1);
    if (remainder > halfway) {
      f16Mant = shifted + 1;
    } else if (remainder === halfway) {
      // Tie: round to even
      f16Mant = (shifted & 1) ? shifted + 1 : shifted;
    } else {
      f16Mant = shifted;
    }
    // If rounding overflows into exp=1, that's okay
    if (f16Mant >= (1 << 10)) {
      f16Exp = 1;
      f16Mant = 0;
    } else {
      f16Mant &= 0x3FF;
    }
  } else if (unbiasedExp > 15) {
    // Overflow: Inf
    f16Exp = 0x1F;
    f16Mant = 0;
  } else {
    // Normal f16
    f16Exp = unbiasedExp + 15;
    // Round 23-bit mantissa to 10 bits with RNE
    const dropped = f32Mant & 0x1FFF;  // lower 13 bits
    const halfway = 0x1000;
    f16Mant = f32Mant >> 13;
    if (dropped > halfway) {
      f16Mant += 1;
    } else if (dropped === halfway) {
      // Tie: round to even
      if (f16Mant & 1) {
        f16Mant += 1;
      }
    }
    // Mantissa overflow -> exponent bump
    if (f16Mant > 0x3FF) {
      f16Mant = 0;
      f16Exp += 1;
      if (f16Exp >= 0x1F) {
        f16Exp = 0x1F;
        f16Mant = 0;
      }
    }
  }

  return (f16Sign << 15) | (f16Exp << 10) | f16Mant;
}

export function encodeFloat16(value, rm = 0) {
  if (Number.isNaN(value)) {
    // Canonical NaN: 0x7E00
    const data = new Uint8Array(2);
    data[0] = 0x00;
    data[1] = 0x7E;
    return { data, exc: NO_EXC };
  }
  if (!Number.isFinite(value)) {
    // +Inf: 0x7C00, -Inf: 0xFC00
    const bits = value > 0 ? 0x7C00 : 0xFC00;
    const data = new Uint8Array(2);
    data[0] = bits & 0xFF;
    data[1] = (bits >> 8) & 0xFF;
    return { data, exc: NO_EXC };
  }
  if (value === 0) {
    const isNeg = Object.is(value, -0);
    const bits = isNeg ? 0x8000 : 0x0000;
    const data = new Uint8Array(2);
    data[0] = bits & 0xFF;
    data[1] = (bits >> 8) & 0xFF;
    return { data, exc: NO_EXC };
  }

  if (rm !== RoundingMode.RNE) {
    return _encodeIeeeDirected(value, 5, 10, 15, rm);
  }

  // RNE
  if (Math.abs(value) >= _OVERFLOW_THRESH_F16) {
    const sign = value < 0 ? -1.0 : 1.0;
    const bits = sign < 0 ? 0xFC00 : 0x7C00;
    const data = new Uint8Array(2);
    data[0] = bits & 0xFF;
    data[1] = (bits >> 8) & 0xFF;
    return { data, exc: exc({ overflow: true, inexact: true }) };
  }

  const f16Bits = _encodeFloat16Rne(value);
  const data = new Uint8Array(2);
  data[0] = f16Bits & 0xFF;
  data[1] = (f16Bits >> 8) & 0xFF;

  const rt = decodeFloat16Bits(f16Bits);
  const overflow = !Number.isFinite(rt) && Number.isFinite(value);
  const expBits = (f16Bits >> 10) & 0x1F;
  const isSub = expBits === 0 && (f16Bits & 0x3FF) !== 0;
  const flushedToZero = rt === 0 && value !== 0;
  const exactSubnormal = 0 < Math.abs(value) && Math.abs(value) < _MIN_NORMAL_F16;
  const underflow = isSub || flushedToZero || exactSubnormal;
  const inexact = rt !== value;

  return {
    data,
    exc: exc({ overflow, underflow, inexact: inexact || overflow }),
  };
}

export function decodeFloat16Bits(bits) {
  const sign = (bits >>> 15) & 1;
  const expField = (bits >>> 10) & 0x1F;
  const mant = bits & 0x3FF;

  if (expField === 0x1F) {
    if (mant !== 0) return NaN;
    return sign ? -Infinity : Infinity;
  }
  if (expField === 0) {
    if (mant === 0) return sign ? -0.0 : 0.0;
    const val = (mant / 1024) * Math.pow(2, -14);
    return sign ? -val : val;
  }
  const val = (1.0 + mant / 1024) * Math.pow(2, expField - 15);
  return sign ? -val : val;
}

export function decodeFloat16(data) {
  const bits = data[0] | (data[1] << 8);
  return decodeFloat16Bits(bits);
}

// ── bfloat16 ────────────────────────────────────────────────────

function _roundF32ToBf16(f32Bits) {
  let upper = (f32Bits >>> 16) & 0xFFFF;
  const lower = f32Bits & 0xFFFF;

  const halfway = 0x8000;
  if (lower > halfway) {
    upper += 1;
  } else if (lower === halfway) {
    if (upper & 1) {
      upper += 1;
    }
  }

  return upper;
}

export function encodeBfloat16(value, rm = 0) {
  if (Number.isNaN(value)) {
    // Canonical NaN: 0x7FC0
    const data = new Uint8Array(2);
    data[0] = 0xC0;
    data[1] = 0x7F;
    return { data, exc: NO_EXC };
  }
  if (!Number.isFinite(value)) {
    // +Inf: 0x7F80, -Inf: 0xFF80
    const data = new Uint8Array(2);
    if (value > 0) {
      data[0] = 0x80;
      data[1] = 0x7F;
    } else {
      data[0] = 0x80;
      data[1] = 0xFF;
    }
    return { data, exc: NO_EXC };
  }
  if (value === 0) {
    // Preserve sign of zero: get from float32
    _f32arr[0] = value;
    const f32Bits = _u32arr[0];
    const upper = (f32Bits >>> 16) & 0xFFFF;
    const data = new Uint8Array(2);
    data[0] = upper & 0xFF;
    data[1] = (upper >> 8) & 0xFF;
    return { data, exc: NO_EXC };
  }

  if (rm !== RoundingMode.RNE) {
    return _encodeIeeeDirected(value, 8, 7, 127, rm);
  }

  // RNE: pack to float32, then round upper 16 bits
  if (Math.abs(value) >= _OVERFLOW_THRESH_F32) {
    const bf16 = value < 0 ? 0xFF80 : 0x7F80;
    const data = new Uint8Array(2);
    data[0] = bf16 & 0xFF;
    data[1] = (bf16 >> 8) & 0xFF;
    return { data, exc: exc({ overflow: true, inexact: true }) };
  }

  _f32arr[0] = value;
  const f32Bits = _u32arr[0];
  const lower = f32Bits & 0xFFFF;

  const upper = _roundF32ToBf16(f32Bits);
  const data = new Uint8Array(2);
  data[0] = upper & 0xFF;
  data[1] = (upper >> 8) & 0xFF;

  // Check if rounding caused overflow to Inf
  const rt = decodeBfloat16(data);
  const overflow = !Number.isFinite(rt) && Number.isFinite(value);
  const inexact = lower !== 0;
  // Underflow: result is subnormal bf16 or flushed to zero
  const bfExp = (upper >> 7) & 0xFF;
  const bfMant = upper & 0x7F;
  const flushed = rt === 0 && value !== 0;
  const underflow = (bfExp === 0 && bfMant !== 0) || flushed;

  return {
    data,
    exc: exc({ overflow, underflow, inexact: inexact || overflow }),
  };
}

export function decodeBfloat16(data) {
  // bfloat16 is the upper 16 bits of float32 in LE
  // So bfloat16 LE bytes become bytes [2:3] of float32 LE
  const upper = data[0] | (data[1] << 8);
  _u32arr[0] = upper << 16;
  return _f32arr[0];
}

// ── OFP8 E4M3 ──────────────────────────────────────────────────

const _E4M3_BIAS = 7;
const _E4M3_EXP_BITS = 4;
const _E4M3_MANT_BITS = 3;
const _E4M3_MAX_EXP = (1 << _E4M3_EXP_BITS) - 1;  // 15
const _E4M3_MAX_FINITE = 448.0;

export function encodeOfp8E4M3(value, rm = 0) {
  if (Number.isNaN(value)) {
    return { data: new Uint8Array([0x7F]), exc: exc({ invalid: true }) };
  }

  let sign = 0;
  if (value < 0 || (value === 0 && Object.is(value, -0))) {
    sign = 1;
    value = -value;
  }

  if (!Number.isFinite(value)) {
    // No Inf in E4M3 -- saturate to max finite
    const byteVal = (sign << 7) | 0x7E;
    return { data: new Uint8Array([byteVal]), exc: exc({ overflow: true, inexact: true }) };
  }

  if (value === 0) {
    return { data: new Uint8Array([sign << 7]), exc: NO_EXC };
  }

  if (value > _E4M3_MAX_FINITE) {
    const byteVal = (sign << 7) | 0x7E;
    return { data: new Uint8Array([byteVal]), exc: exc({ overflow: true, inexact: true }) };
  }

  const { byteVal, exc: mExc } = _encodeMiniFloat(
    value, sign, _E4M3_EXP_BITS, _E4M3_MANT_BITS, _E4M3_BIAS,
    false, 0x7F, rm,
  );
  return { data: new Uint8Array([byteVal]), exc: mExc };
}

export function decodeOfp8E4M3(byteVal) {
  if (typeof byteVal !== 'number') byteVal = byteVal[0];
  const sign = (byteVal >> 7) & 1;
  const expField = (byteVal >> _E4M3_MANT_BITS) & _E4M3_MAX_EXP;
  const mant = byteVal & ((1 << _E4M3_MANT_BITS) - 1);

  if (expField === _E4M3_MAX_EXP && mant === (1 << _E4M3_MANT_BITS) - 1) {
    return NaN;
  }

  if (expField === 0) {
    if (mant === 0) return sign ? -0.0 : 0.0;
    const val = (mant / (1 << _E4M3_MANT_BITS)) * Math.pow(2, 1 - _E4M3_BIAS);
    return sign ? -val : val;
  }

  const val = (1.0 + mant / (1 << _E4M3_MANT_BITS)) * Math.pow(2, expField - _E4M3_BIAS);
  return sign ? -val : val;
}

// ── OFP8 E5M2 ──────────────────────────────────────────────────

const _E5M2_BIAS = 15;
const _E5M2_EXP_BITS = 5;
const _E5M2_MANT_BITS = 2;
const _E5M2_MAX_EXP = (1 << _E5M2_EXP_BITS) - 1;  // 31
const _E5M2_MAX_FINITE = 57344.0;

export function encodeOfp8E5M2(value, rm = 0) {
  if (Number.isNaN(value)) {
    // Canonical NaN: exp=31, mant=1 (quiet NaN) = 0x7D
    return { data: new Uint8Array([0x7D]), exc: exc({ invalid: true }) };
  }

  let sign = 0;
  if (value < 0 || (value === 0 && Object.is(value, -0))) {
    sign = 1;
    value = -value;
  }

  if (!Number.isFinite(value)) {
    const byteVal = (sign << 7) | (_E5M2_MAX_EXP << _E5M2_MANT_BITS);
    return { data: new Uint8Array([byteVal]), exc: NO_EXC };
  }

  if (value === 0) {
    return { data: new Uint8Array([sign << 7]), exc: NO_EXC };
  }

  const { byteVal, exc: mExc } = _encodeMiniFloat(
    value, sign, _E5M2_EXP_BITS, _E5M2_MANT_BITS, _E5M2_BIAS,
    true, null, rm,
  );
  return { data: new Uint8Array([byteVal]), exc: mExc };
}

export function decodeOfp8E5M2(byteVal) {
  if (typeof byteVal !== 'number') byteVal = byteVal[0];
  const sign = (byteVal >> 7) & 1;
  const expField = (byteVal >> _E5M2_MANT_BITS) & _E5M2_MAX_EXP;
  const mant = byteVal & ((1 << _E5M2_MANT_BITS) - 1);

  if (expField === _E5M2_MAX_EXP) {
    if (mant === 0) return sign ? -Infinity : Infinity;
    return NaN;
  }

  if (expField === 0) {
    if (mant === 0) return sign ? -0.0 : 0.0;
    const val = (mant / (1 << _E5M2_MANT_BITS)) * Math.pow(2, 1 - _E5M2_BIAS);
    return sign ? -val : val;
  }

  const val = (1.0 + mant / (1 << _E5M2_MANT_BITS)) * Math.pow(2, expField - _E5M2_BIAS);
  return sign ? -val : val;
}

// ── Generic mini-float encoder ──────────────────────────────────

function _overflowReturnsInf(rm, sign) {
  if (rm === RoundingMode.RTZ) return false;
  if (rm === RoundingMode.RDN) return sign === 1;
  if (rm === RoundingMode.RUP) return sign === 0;
  return true;  // RNE
}

function _overflowResult(sign, expBits, mantBits, maxExp,
                         maxNormalBiased, hasInf, nanPattern, rm) {
  if (hasInf && _overflowReturnsInf(rm, sign)) {
    const byteVal = (sign << (expBits + mantBits)) | (maxExp << mantBits);
    return { byteVal, exc: exc({ overflow: true, inexact: true }) };
  }
  let maxMant = (1 << mantBits) - 1;
  if (nanPattern !== null) {
    maxMant -= 1;
  }
  const byteVal = (sign << (expBits + mantBits))
                | (maxNormalBiased << mantBits)
                | maxMant;
  return { byteVal, exc: exc({ overflow: true, inexact: true }) };
}

function _encodeMiniFloat(absVal, sign, expBits, mantBits, bias,
                          hasInf, nanPattern, rm) {
  const maxExp = (1 << expBits) - 1;
  const maxNormalBiased = hasInf ? maxExp - 1 : maxExp;

  // Compute unbiased exponent (absVal > 0 guaranteed by callers)
  const log2Val = Math.floor(Math.log2(absVal));
  let biasedExp = log2Val + bias;
  let mantInt;
  let underflow;

  if (biasedExp <= 0) {
    // Denormalized number
    biasedExp = 0;
    const scale = Math.pow(2, 1 - bias);
    const mantFrac = absVal / scale;
    mantInt = _roundMantissa(mantFrac, mantBits, rm, sign);
    // Check if rounding promoted to normal
    if (mantInt >= (1 << mantBits)) {
      biasedExp = 1;
      mantInt -= 1 << mantBits;
    }
    underflow = true;
  } else if (biasedExp > maxNormalBiased) {
    return _overflowResult(sign, expBits, mantBits, maxExp,
                           maxNormalBiased, hasInf, nanPattern, rm);
  } else {
    // Normal number
    const significand = absVal / Math.pow(2, log2Val);  // 1.xxx
    const mantFrac = Math.max(0.0, significand - 1.0);
    mantInt = _roundMantissa(mantFrac, mantBits, rm, sign);
    // Rounding may cause mantissa overflow
    if (mantInt >= (1 << mantBits)) {
      mantInt = 0;
      biasedExp += 1;
      if (biasedExp > maxNormalBiased) {
        return _overflowResult(sign, expBits, mantBits, maxExp,
                               maxNormalBiased, hasInf, nanPattern, rm);
      }
    }
    // Check for E4M3 NaN collision
    if (!hasInf && nanPattern !== null) {
      const candidate = (biasedExp << mantBits) | mantInt;
      if (candidate === (nanPattern & ((1 << (expBits + mantBits)) - 1))) {
        mantInt -= 1;
      }
    }
    underflow = false;
  }

  const byteVal = (sign << (expBits + mantBits))
                | (biasedExp << mantBits)
                | mantInt;

  // Recompute inexact by round-tripping
  let rtVal;
  if (biasedExp === 0) {
    rtVal = (mantInt / (1 << mantBits)) * Math.pow(2, 1 - bias);
  } else {
    rtVal = (1.0 + mantInt / (1 << mantBits)) * Math.pow(2, biasedExp - bias);
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
    absVal, sign, expBits, mantBits, bias,
    true, null, rm,
  );
  const width = 1 + expBits + mantBits;
  const numBytes = width >> 3;
  const data = new Uint8Array(numBytes);
  for (let i = 0; i < numBytes; i++) {
    data[i] = (bits >> (i * 8)) & 0xFF;
  }
  return { data, exc: mExc };
}

function _roundMantissa(frac, mantBits, rm, sign) {
  const scale = 1 << mantBits;
  const scaled = frac * scale;
  const floorVal = Math.floor(scaled);
  const remainder = scaled - floorVal;

  if (remainder === 0.0) return floorVal;

  if (rm === RoundingMode.RNE) {
    if (remainder > 0.5) return floorVal + 1;
    if (remainder < 0.5) return floorVal;
    // Tie: round to even
    return (floorVal & 1) ? floorVal + 1 : floorVal;
  }
  if (rm === RoundingMode.RTZ) {
    return floorVal;
  }
  if (rm === RoundingMode.RDN) {
    // Toward -Inf: if negative, round away from zero (up magnitude)
    return sign ? floorVal + 1 : floorVal;
  }
  // RUP: toward +Inf: if positive, round away from zero
  return sign ? floorVal : floorVal + 1;
}

// ── Dispatcher functions ────────────────────────────────────────

export function floatToBytes(value, fmt, rm = 0) {
  if (fmt === FP_FMT_F)  return encodeFloat32(value, rm);
  if (fmt === FP_FMT_H)  return encodeFloat16(value, rm);
  if (fmt === FP_FMT_BF) return encodeBfloat16(value, rm);
  if (fmt === FP_FMT_O3) return encodeOfp8E4M3(value, rm);
  if (fmt === FP_FMT_O2) return encodeOfp8E5M2(value, rm);
  throw new Error(`unsupported FP format code: ${fmt}`);
}

export function bytesToFloat(data, fmt) {
  if (fmt === FP_FMT_F)  return decodeFloat32(data);
  if (fmt === FP_FMT_H)  return decodeFloat16(data);
  if (fmt === FP_FMT_BF) return decodeBfloat16(data);
  if (fmt === FP_FMT_O3) return decodeOfp8E4M3(data[0]);
  if (fmt === FP_FMT_O2) return decodeOfp8E5M2(data[0]);
  throw new Error(`unsupported FP format code: ${fmt}`);
}

// ── FP arithmetic helpers ───────────────────────────────────────

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

export function fpAdd(a, b, fmt, rm = 0) {
  if (Number.isNaN(a) || Number.isNaN(b)) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  // Inf - Inf = NaN
  if (!Number.isFinite(a) && !Number.isFinite(b) && a !== b) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  return _addCore(a, b, fmt, rm);
}

export function fpSub(a, b, fmt, rm = 0) {
  if (Number.isNaN(a) || Number.isNaN(b)) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  // Inf - Inf = NaN
  if (!Number.isFinite(a) && !Number.isFinite(b) && a === b) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  return _addCore(a, -b, fmt, rm);
}

export function fpMul(a, b, fmt, rm = 0) {
  if (Number.isNaN(a) || Number.isNaN(b)) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  // 0 * Inf or Inf * 0 = NaN
  if ((a === 0 && !Number.isFinite(b)) || (!Number.isFinite(a) && b === 0)) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  const result = a * b;
  return _reEncode(result, fmt, rm);
}

export function fpDiv(a, b, fmt, rm = 0) {
  if (Number.isNaN(a) || Number.isNaN(b)) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  // 0/0 = NaN (invalid)
  if (a === 0 && b === 0) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  // Inf/Inf = NaN (invalid)
  if (!Number.isFinite(a) && !Number.isFinite(b)) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  // finite/0 = Inf (divZero)
  if (b === 0) {
    const signA = copysign(1.0, a);
    const signB = copysign(1.0, b);
    const sign = signA * signB;
    return { result: copysign(Infinity, sign), exc: exc({ divZero: true }) };
  }
  const result = a / b;
  return _reEncode(result, fmt, rm);
}

export function fpSqrt(value, fmt, rm = 0) {
  if (Number.isNaN(value)) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  if (value < 0) {
    return { result: NaN, exc: exc({ invalid: true }) };
  }
  if (value === 0) {
    return { result: copysign(0.0, value), exc: NO_EXC };
  }
  if (!Number.isFinite(value)) {
    return { result: Infinity, exc: NO_EXC };
  }
  const result = Math.sqrt(value);
  return _reEncode(result, fmt, rm);
}

export function fpCmp(a, b) {
  if (Number.isNaN(a) || Number.isNaN(b)) {
    return { zero: true, carry: true, exc: exc({ invalid: true }) };
  }
  if (a === b) {  // handles +0 === -0
    return { zero: true, carry: false, exc: NO_EXC };
  }
  if (a < b) {
    return { zero: false, carry: true, exc: NO_EXC };
  }
  return { zero: false, carry: false, exc: NO_EXC };
}

// ── Bit manipulation ────────────────────────────────────────────

export function fpAbs(rawBits, width) {
  const signMask = 1 << (width - 1);
  return rawBits & ~signMask;
}

export function fpNeg(rawBits, width) {
  const signMask = 1 << (width - 1);
  return (rawBits ^ signMask) >>> 0;
}

// ── Classification ──────────────────────────────────────────────

const _FMT_SHAPE = {
  [FP_FMT_F]:  [23, 8],
  [FP_FMT_H]:  [10, 5],
  [FP_FMT_BF]: [7,  8],
  [FP_FMT_O3]: [3,  4],
  [FP_FMT_O2]: [2,  5],
};

function _isSubnormal(rawBits, width, fmt) {
  const shape = _FMT_SHAPE[fmt];
  if (!shape) return false;
  const [mantBits, expBits] = shape;
  const expField = (rawBits >> mantBits) & ((1 << expBits) - 1);
  const mant = rawBits & ((1 << mantBits) - 1);
  return expField === 0 && mant !== 0;
}

export function fpClassify(value, rawBits, width, fmt) {
  let result = 0;
  const signMask = 1 << (width - 1);
  if (rawBits & signMask) {
    result |= 0x40;  // bit 6: NEG
  }

  if (Number.isNaN(value)) {
    result |= 0x10;  // bit 4: QNAN
    return result;
  }

  if (!Number.isFinite(value)) {
    result |= 0x08;  // bit 3: INF
    return result;
  }

  if (value === 0) {
    result |= 0x01;  // bit 0: ZERO
    return result;
  }

  if (_isSubnormal(rawBits, width, fmt)) {
    result |= 0x02;  // bit 1: SUB
  } else {
    result |= 0x04;  // bit 2: NORM
  }

  return result;
}
