/**
 * FP arithmetic operations and re-exports of format encode/decode.
 */

export {
    RoundingMode,
    encodeFloat32,
    decodeFloat32,
    encodeFloat16,
    decodeFloat16Bits,
    decodeFloat16,
    encodeBfloat16,
    decodeBfloat16,
    encodeOfp8E4M3,
    decodeOfp8E4M3,
    encodeOfp8E5M2,
    decodeOfp8E5M2,
    floatToBytes,
    bytesToFloat,
} from "./fp-formats.js";

import { FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2 } from "./isa.js";

import { NO_EXC, exc, excReplace, nextafter, copysign, floatToBytes, bytesToFloat } from "./fp-formats.js";

// ── FP arithmetic helpers ───────────────────────────────────────

/** Canonical NaN-invalid result for arithmetic operations. */
const _NAN_INVALID = Object.freeze({ result: NaN, exc: exc({ invalid: true }) });

const _FMT_SHAPE = {
    [FP_FMT_F]: [23, 8],
    [FP_FMT_H]: [10, 5],
    [FP_FMT_BF]: [7, 8],
    [FP_FMT_O3]: [3, 4],
    [FP_FMT_O2]: [2, 5],
};

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
        return _NAN_INVALID;
    }
    // Inf - Inf = NaN
    if (!Number.isFinite(a) && !Number.isFinite(b) && a !== b) {
        return _NAN_INVALID;
    }
    return _addCore(a, b, fmt, rm);
}

export function fpSub(a, b, fmt, rm = 0) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
        return _NAN_INVALID;
    }
    // Inf - Inf = NaN
    if (!Number.isFinite(a) && !Number.isFinite(b) && a === b) {
        return _NAN_INVALID;
    }
    return _addCore(a, -b, fmt, rm);
}

export function fpMul(a, b, fmt, rm = 0) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
        return _NAN_INVALID;
    }
    // 0 * Inf or Inf * 0 = NaN
    if ((a === 0 && !Number.isFinite(b)) || (!Number.isFinite(a) && b === 0)) {
        return _NAN_INVALID;
    }
    const result = a * b;
    return _reEncode(result, fmt, rm);
}

export function fpDiv(a, b, fmt, rm = 0) {
    if (Number.isNaN(a) || Number.isNaN(b)) {
        return _NAN_INVALID;
    }
    // 0/0 = NaN (invalid)
    if (a === 0 && b === 0) {
        return _NAN_INVALID;
    }
    // Inf/Inf = NaN (invalid)
    if (!Number.isFinite(a) && !Number.isFinite(b)) {
        return _NAN_INVALID;
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
    if (Number.isNaN(value) || value < 0) {
        return _NAN_INVALID;
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
    if (a === b) {
        // handles +0 === -0
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

function _isSubnormal(rawBits, _width, fmt) {
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
        result |= 0x40; // bit 6: NEG
    }

    if (Number.isNaN(value)) {
        result |= 0x10; // bit 4: QNAN
        return result;
    }

    if (!Number.isFinite(value)) {
        result |= 0x08; // bit 3: INF
        return result;
    }

    if (value === 0) {
        result |= 0x01; // bit 0: ZERO
        return result;
    }

    if (_isSubnormal(rawBits, width, fmt)) {
        result |= 0x02; // bit 1: SUB
    } else {
        result |= 0x04; // bit 2: NORM
    }

    return result;
}
