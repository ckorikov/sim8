"""IEEE 754 floating-point format encode/decode.

Supports: float32, float16, bfloat16, OFP8 E4M3, OFP8 E5M2.
No simulator dependencies -- used by both assembler and simulator.
"""

from __future__ import annotations

import math
import struct
from collections.abc import Callable
from typing import NamedTuple, cast

from pysim8.constants import (
    FP_FMT_BF as _FMT_BF,
)
from pysim8.constants import (
    FP_FMT_F as _FMT_F,
)
from pysim8.constants import (
    FP_FMT_H as _FMT_H,
)
from pysim8.constants import (
    FP_FMT_O2 as _FMT_O2,
)
from pysim8.constants import (
    FP_FMT_O3 as _FMT_O3,
)

__all__ = [
    "FpExceptions",
    "float_to_bytes",
    "bytes_to_float",
    "encode_float32",
    "decode_float32",
    "encode_float16",
    "decode_float16",
    "encode_bfloat16",
    "decode_bfloat16",
    "encode_ofp8_e4m3",
    "decode_ofp8_e4m3",
    "encode_ofp8_e5m2",
    "decode_ofp8_e5m2",
    "RoundingMode",
    "fp_add",
    "fp_sub",
    "fp_mul",
    "fp_div",
    "fp_sqrt",
    "fp_cmp",
    "fp_abs",
    "fp_neg",
    "fp_classify",
]


class RoundingMode:
    """Rounding mode constants matching FPCR.RM."""

    RNE = 0  # Round to Nearest, ties to Even
    RTZ = 1  # Round toward Zero
    RDN = 2  # Round toward -Inf
    RUP = 3  # Round toward +Inf


class FpExceptions(NamedTuple):
    """IEEE 754 exception flags from one operation."""

    invalid: bool = False  # NV
    div_zero: bool = False  # DZ
    overflow: bool = False  # OF
    underflow: bool = False  # UF
    inexact: bool = False  # NX


NO_EXC = FpExceptions()

# ── IEEE 754 boundary constants ──────────────────────────────────
# Minimum positive normal: 2^-(bias-1)
_MIN_NORMAL_F32 = 1.1754943508222875e-38  # 2^-126
_MIN_NORMAL_F16 = 6.103515625e-05  # 2^-14
# RNE overflow threshold: MAX + half ULP (values at or above round to inf)
_OVERFLOW_THRESH_F32 = 3.4028235677973366e38  # (2-2^-23)*2^127 + 2^103
_OVERFLOW_THRESH_F16 = 65520.0  # 65504 + 16 (half ULP at max)


# ── IEEE struct-based encoder (float32/float16 RNE) ──────────────


class _IeeeParams(NamedTuple):
    """Parameters for a struct-based IEEE format."""

    pack_fmt: str  # struct format string
    exp_bits: int
    mant_bits: int
    bias: int
    overflow_thresh: float
    min_normal: float


_F32_PARAMS = _IeeeParams("<f", 8, 23, 127, _OVERFLOW_THRESH_F32, _MIN_NORMAL_F32)
_F16_PARAMS = _IeeeParams("<e", 5, 10, 15, _OVERFLOW_THRESH_F16, _MIN_NORMAL_F16)


def _encode_ieee_rne(
    value: float,
    p: _IeeeParams,
) -> tuple[bytes, FpExceptions]:
    """Encode a finite non-zero float using struct.pack with RNE rounding.

    Common path for float32 and float16.
    """
    if abs(value) >= p.overflow_thresh:
        sign = -1.0 if value < 0 else 1.0
        data = struct.pack(p.pack_fmt, math.copysign(math.inf, sign))
        return data, FpExceptions(overflow=True, inexact=True)
    data = struct.pack(p.pack_fmt, value)
    rt = struct.unpack(p.pack_fmt, data)[0]
    overflow = math.isinf(rt) and not math.isinf(value)
    bits = int.from_bytes(data, "little")
    exp_mask = (1 << p.exp_bits) - 1
    mant_mask = (1 << p.mant_bits) - 1
    exp_val = (bits >> p.mant_bits) & exp_mask
    is_subnormal = exp_val == 0 and (bits & mant_mask) != 0
    flushed_to_zero = rt == 0.0 and value != 0.0
    # IEEE 754 §7.5: underflow "before rounding" — exact value in
    # subnormal range even if rounding pushes it to normal.
    exact_subnormal = 0 < abs(value) < p.min_normal
    underflow = is_subnormal or flushed_to_zero or exact_subnormal
    inexact = rt != value
    return data, FpExceptions(
        overflow=overflow,
        underflow=underflow,
        inexact=inexact or overflow,
    )


# ── float32 ──────────────────────────────────────────────────────


def encode_float32(
    value: float,
    rm: int = 0,
) -> tuple[bytes, FpExceptions]:
    """Encode Python float as little-endian float32 bytes."""
    if math.isnan(value) or math.isinf(value) or value == 0.0:
        return struct.pack("<f", value), NO_EXC
    if rm != RoundingMode.RNE:
        return _encode_ieee_directed(value, 8, 23, 127, rm)
    return _encode_ieee_rne(value, _F32_PARAMS)


def decode_float32(data: bytes) -> float:
    """Decode little-endian float32 bytes to Python float."""
    return cast(float, struct.unpack("<f", data)[0])


# ── float16 ──────────────────────────────────────────────────────


def encode_float16(
    value: float,
    rm: int = 0,
) -> tuple[bytes, FpExceptions]:
    """Encode Python float as little-endian float16 (IEEE 754) bytes."""
    if math.isnan(value) or math.isinf(value) or value == 0.0:
        return struct.pack("<e", value), NO_EXC
    if rm != RoundingMode.RNE:
        return _encode_ieee_directed(value, 5, 10, 15, rm)
    return _encode_ieee_rne(value, _F16_PARAMS)


def decode_float16(data: bytes) -> float:
    """Decode little-endian float16 bytes to Python float."""
    return cast(float, struct.unpack("<e", data)[0])


# ── bfloat16 ─────────────────────────────────────────────────────


def _round_f32_to_bf16(f32_bits: int) -> int:
    """Round float32 bits to bfloat16 (top 16 bits) with RNE rounding."""
    upper = (f32_bits >> 16) & 0xFFFF
    lower = f32_bits & 0xFFFF

    # Round to nearest, ties to even
    halfway = 0x8000
    if lower > halfway:
        upper += 1
    elif lower == halfway:
        if upper & 1:
            upper += 1

    return upper


def encode_bfloat16(
    value: float,
    rm: int = 0,
) -> tuple[bytes, FpExceptions]:
    """Encode Python float as little-endian bfloat16 bytes.

    bfloat16 = top 16 bits of float32, with rounding on the
    truncated lower 16 bits.
    """
    if math.isnan(value):
        # Canonical NaN: 0x7FC0
        return b"\xc0\x7f", NO_EXC
    if math.isinf(value):
        if value > 0:
            return b"\x80\x7f", NO_EXC
        return b"\x80\xff", NO_EXC
    if value == 0.0:
        # Preserve sign of zero
        return struct.pack("<f", value)[2:], NO_EXC

    if rm != RoundingMode.RNE:
        return _encode_ieee_directed(value, 8, 7, 127, rm)

    # RNE: pack to float32, then round upper 16 bits.
    # Guard overflow: struct.pack("<f") raises for |value| > MAX_F32.
    if abs(value) >= _OVERFLOW_THRESH_F32:
        bf16 = 0xFF80 if value < 0 else 0x7F80  # ±Inf
        return bf16.to_bytes(2, "little"), FpExceptions(
            overflow=True,
            inexact=True,
        )

    f32_bytes = struct.pack("<f", value)
    f32_bits = int.from_bytes(f32_bytes, "little")
    lower = f32_bits & 0xFFFF

    upper = _round_f32_to_bf16(f32_bits)
    data = upper.to_bytes(2, "little")

    # Check if rounding caused overflow to Inf
    rt = decode_bfloat16(data)
    overflow = math.isinf(rt) and not math.isinf(value)
    inexact = lower != 0
    # Underflow: result is subnormal bf16 or flushed to zero
    bf_exp = (upper >> 7) & 0xFF
    bf_mant = upper & 0x7F
    flushed = rt == 0.0 and value != 0.0
    underflow = (bf_exp == 0 and bf_mant != 0) or flushed

    return data, FpExceptions(
        overflow=overflow,
        underflow=underflow,
        inexact=inexact or overflow,
    )


def decode_bfloat16(data: bytes) -> float:
    """Decode little-endian bfloat16 bytes to Python float.

    Pad with 2 zero bytes to form float32, then unpack.
    """
    # bfloat16 is the upper 16 bits of float32 in LE
    # so bfloat16 LE bytes go at positions [2:3] of float32 LE
    padded = b"\x00\x00" + data[:2]
    return cast(float, struct.unpack("<f", padded)[0])


# ── Generic mini-float decoder ────────────────────────────────────


def _decode_mini_float(
    byte_val: int,
    exp_bits: int,
    mant_bits: int,
    bias: int,
    *,
    has_inf: bool = False,
    nan_pred: Callable[[int, int], bool] | None = None,
) -> float:
    """Decode a mini-float byte to Python float.

    Args:
        byte_val: Raw byte value.
        exp_bits: Number of exponent bits.
        mant_bits: Number of mantissa bits.
        bias: Exponent bias.
        has_inf: If True, max_exp with mant=0 is Inf, mant!=0 is NaN.
        nan_pred: Custom NaN predicate(exp, mant). If None, uses has_inf rule.
    """
    sign = (byte_val >> (exp_bits + mant_bits)) & 1
    max_exp = (1 << exp_bits) - 1
    exp = (byte_val >> mant_bits) & max_exp
    mant = byte_val & ((1 << mant_bits) - 1)

    # Special values
    if nan_pred is not None:
        if nan_pred(exp, mant):
            return float("nan")
    elif has_inf and exp == max_exp:
        if mant == 0:
            return float("-inf") if sign else float("inf")
        return float("nan")

    # Zero / denorm / normal
    if exp == 0:
        if mant == 0:
            return -0.0 if sign else 0.0
        val: float = (mant / (1 << mant_bits)) * float(2 ** (1 - bias))
    else:
        val = (1.0 + mant / (1 << mant_bits)) * float(2 ** (exp - bias))

    return -val if sign else val


# ── OFP8 E4M3 ───────────────────────────────────────────────────

# E4M3: bias=7, 4-bit exponent, 3-bit mantissa.
# No Inf representation. NaN = s_1111_111 (only pattern).
# exp=1111, mant=000..110 → normal finite values.
# Max finite: exp=1111, mant=110 → (1 + 6/8) * 2^(15-7) = 448.
_E4M3_BIAS = 7
_E4M3_EXP_BITS = 4
_E4M3_MANT_BITS = 3
_E4M3_MAX_EXP = (1 << _E4M3_EXP_BITS) - 1  # 15
_E4M3_MAX_FINITE = 448.0  # (1 + 6/8) * 2^8


def encode_ofp8_e4m3(
    value: float,
    rm: int = 0,
) -> tuple[bytes, FpExceptions]:
    """Encode Python float as OFP8 E4M3 (1 byte)."""
    if math.isnan(value):
        return b"\x7f", FpExceptions(invalid=True)

    sign = 0
    if value < 0 or (value == 0.0 and math.copysign(1.0, value) < 0):
        sign = 1
        value = -value

    if math.isinf(value):
        # No Inf in E4M3 -- saturate to max finite, set overflow
        byte_val = (sign << 7) | 0x7E  # exp=1111, mant=110
        return bytes([byte_val]), FpExceptions(overflow=True, inexact=True)

    if value == 0.0:
        return bytes([sign << 7]), NO_EXC

    # Overflow check
    if value > _E4M3_MAX_FINITE:
        byte_val = (sign << 7) | 0x7E
        return bytes([byte_val]), FpExceptions(
            overflow=True,
            inexact=True,
        )

    # Encode: find exponent and mantissa
    result_byte, exc = _encode_mini_float(
        value,
        sign,
        _E4M3_EXP_BITS,
        _E4M3_MANT_BITS,
        _E4M3_BIAS,
        has_inf=False,
        nan_pattern=0x7F,
        rm=rm,
    )
    return bytes([result_byte]), exc


def decode_ofp8_e4m3(byte_val: int) -> float:
    """Decode OFP8 E4M3 byte to Python float."""
    return _decode_mini_float(
        byte_val,
        _E4M3_EXP_BITS,
        _E4M3_MANT_BITS,
        _E4M3_BIAS,
        nan_pred=lambda e, m: e == _E4M3_MAX_EXP and m == (1 << _E4M3_MANT_BITS) - 1,
    )


# ── OFP8 E5M2 ───────────────────────────────────────────────────

# E5M2: bias=15, standard IEEE 754 with 5-bit exp, 2-bit mantissa.
# Inf: exp=31, mant=0; NaN: exp=31, mant!=0.
# Max finite: exp=30, mant=11 → (1 + 3/4) * 2^(30-15) = 57344.
_E5M2_BIAS = 15
_E5M2_EXP_BITS = 5
_E5M2_MANT_BITS = 2
_E5M2_MAX_EXP = (1 << _E5M2_EXP_BITS) - 1  # 31
_E5M2_MAX_FINITE = 57344.0  # (1 + 3/4) * 2^15


def encode_ofp8_e5m2(
    value: float,
    rm: int = 0,
) -> tuple[bytes, FpExceptions]:
    """Encode Python float as OFP8 E5M2 (1 byte)."""
    if math.isnan(value):
        # Canonical NaN: exp=31, mant=1 (quiet NaN)
        return b"\x7d", FpExceptions(invalid=True)

    sign = 0
    if value < 0 or (value == 0.0 and math.copysign(1.0, value) < 0):
        sign = 1
        value = -value

    if math.isinf(value):
        byte_val = (sign << 7) | (_E5M2_MAX_EXP << _E5M2_MANT_BITS)
        return bytes([byte_val]), NO_EXC

    if value == 0.0:
        return bytes([sign << 7]), NO_EXC

    result_byte, exc = _encode_mini_float(
        value,
        sign,
        _E5M2_EXP_BITS,
        _E5M2_MANT_BITS,
        _E5M2_BIAS,
        has_inf=True,
        nan_pattern=None,
        rm=rm,
    )
    return bytes([result_byte]), exc


def decode_ofp8_e5m2(byte_val: int) -> float:
    """Decode OFP8 E5M2 byte to Python float."""
    return _decode_mini_float(
        byte_val,
        _E5M2_EXP_BITS,
        _E5M2_MANT_BITS,
        _E5M2_BIAS,
        has_inf=True,
    )


# ── Generic mini-float encoder ───────────────────────────────────


def _overflow_returns_inf(rm: int, sign: int) -> bool:
    """Whether overflow should produce Inf (True) or MAX (False)."""
    if rm == RoundingMode.RTZ:
        return False
    if rm == RoundingMode.RDN:
        return sign == 1  # -Inf for negative, MAX for positive
    if rm == RoundingMode.RUP:
        return sign == 0  # +Inf for positive, -MAX for negative
    return True  # RNE: always Inf


def _overflow_result(
    sign: int,
    exp_bits: int,
    mant_bits: int,
    max_exp: int,
    max_normal_biased: int,
    has_inf: bool,
    nan_pattern: int | None,
    rm: int,
) -> tuple[int, FpExceptions]:
    """Produce the overflow result (Inf or MAX) based on rounding mode."""
    if has_inf and _overflow_returns_inf(rm, sign):
        byte_val = (sign << (exp_bits + mant_bits)) | (max_exp << mant_bits)
        return byte_val, FpExceptions(overflow=True, inexact=True)
    max_mant = (1 << mant_bits) - 1
    if nan_pattern is not None:
        max_mant -= 1
    byte_val = (sign << (exp_bits + mant_bits)) | (max_normal_biased << mant_bits) | max_mant
    return byte_val, FpExceptions(overflow=True, inexact=True)


def _encode_mini_float(
    abs_val: float,
    sign: int,
    exp_bits: int,
    mant_bits: int,
    bias: int,
    *,
    has_inf: bool,
    nan_pattern: int | None,
    rm: int,
) -> tuple[int, FpExceptions]:
    """Encode a positive float into a mini-float format.

    Returns (byte_value, exceptions).
    """
    max_exp = (1 << exp_bits) - 1
    # For formats with Inf, max stored normal exponent = max_exp - 1
    # For E4M3 (no Inf), max stored exponent = max_exp (but NaN
    # steals one pattern)
    if has_inf:
        max_normal_biased = max_exp - 1
    else:
        max_normal_biased = max_exp

    # Compute unbiased exponent (abs_val > 0 guaranteed by callers)
    log2_val = math.floor(math.log2(abs_val))

    biased_exp = log2_val + bias

    if biased_exp <= 0:
        # Denormalized number
        biased_exp = 0
        # Denorm: value = mantissa_frac * 2^(1-bias)
        scale = 2 ** (1 - bias)
        mant_frac = abs_val / scale
        mant_int = _round_mantissa(
            mant_frac,
            mant_bits,
            rm,
            sign,
            is_denorm=True,
        )
        # Check if rounding promoted to normal
        if mant_int >= (1 << mant_bits):
            biased_exp = 1
            mant_int -= 1 << mant_bits
        underflow = True
    elif biased_exp > max_normal_biased:
        return _overflow_result(
            sign,
            exp_bits,
            mant_bits,
            max_exp,
            max_normal_biased,
            has_inf,
            nan_pattern,
            rm,
        )
    else:
        # Normal number
        significand = abs_val / (2**log2_val)  # 1.xxx
        # Clamp to [0, 1) — float64 division may produce tiny negative
        mant_frac = max(0.0, significand - 1.0)
        mant_int = _round_mantissa(
            mant_frac,
            mant_bits,
            rm,
            sign,
            is_denorm=False,
        )
        # Rounding may cause mantissa overflow
        if mant_int >= (1 << mant_bits):
            mant_int = 0
            biased_exp += 1
            if biased_exp > max_normal_biased:
                return _overflow_result(
                    sign,
                    exp_bits,
                    mant_bits,
                    max_exp,
                    max_normal_biased,
                    has_inf,
                    nan_pattern,
                    rm,
                )
        # Check for E4M3 NaN collision (defensive — currently unreachable
        # because encode_ofp8_e4m3 catches overflow before _encode_mini_float)
        if not has_inf and nan_pattern is not None:
            candidate = (biased_exp << mant_bits) | mant_int
            if candidate == (nan_pattern & ((1 << (exp_bits + mant_bits)) - 1)):
                mant_int -= 1
        underflow = False

    byte_val = (sign << (exp_bits + mant_bits)) | (biased_exp << mant_bits) | mant_int

    # Recompute inexact by round-tripping
    if biased_exp == 0:
        rt_val = (mant_int / (1 << mant_bits)) * (2 ** (1 - bias))
    else:
        rt_val = (1.0 + mant_int / (1 << mant_bits)) * (2 ** (biased_exp - bias))
    inexact = rt_val != abs_val

    return byte_val, FpExceptions(
        underflow=underflow,
        inexact=inexact,
    )


def _encode_ieee_directed(
    value: float,
    exp_bits: int,
    mant_bits: int,
    bias: int,
    rm: int,
) -> tuple[bytes, FpExceptions]:
    """Encode a float with directed rounding (non-RNE) for IEEE formats.

    Works for float32 (8/23/127) and float16 (5/10/15).
    """
    sign = 0
    abs_val = value
    if value < 0:
        sign = 1
        abs_val = -value
    bits, exc = _encode_mini_float(
        abs_val,
        sign,
        exp_bits,
        mant_bits,
        bias,
        has_inf=True,
        nan_pattern=None,
        rm=rm,
    )
    width = 1 + exp_bits + mant_bits
    data = bits.to_bytes(width // 8, "little")
    return data, exc


def _round_mantissa(
    frac: float,
    mant_bits: int,
    rm: int,
    sign: int,
    *,
    is_denorm: bool,
) -> int:
    """Round a fractional mantissa value to mant_bits integer bits.

    For normal numbers, frac is in [0, 1).
    For denormals, frac is in [0, 1).
    Returns integer mantissa in [0, 2^mant_bits].
    """
    scale = 1 << mant_bits
    scaled = frac * scale
    floor_val = int(math.floor(scaled))
    remainder = scaled - floor_val

    if remainder == 0.0:
        return floor_val

    if rm == RoundingMode.RNE:
        if remainder > 0.5:
            return floor_val + 1
        if remainder < 0.5:
            return floor_val
        # Tie: round to even
        if floor_val & 1:
            return floor_val + 1
        return floor_val
    elif rm == RoundingMode.RTZ:
        return floor_val
    elif rm == RoundingMode.RDN:
        # Toward -Inf: if negative, round away from zero (up magnitude)
        if sign:
            return floor_val + 1
        return floor_val
    else:
        # RUP: toward +Inf — if positive, round away from zero
        if not sign:
            return floor_val + 1
        return floor_val


# ── Dispatch tables ──────────────────────────────────────────────

_ENCODERS: dict[int, Callable[[float, int], tuple[bytes, FpExceptions]]] = {
    _FMT_F: encode_float32,
    _FMT_H: encode_float16,
    _FMT_BF: encode_bfloat16,
    _FMT_O3: encode_ofp8_e4m3,
    _FMT_O2: encode_ofp8_e5m2,
}

# Byte width per format (for decoder slicing)
_FMT_BYTES: dict[int, int] = {
    _FMT_F: 4,
    _FMT_H: 2,
    _FMT_BF: 2,
    _FMT_O3: 1,
    _FMT_O2: 1,
}

_DECODERS_RAW: dict[int, Callable[..., float]] = {
    _FMT_F: decode_float32,
    _FMT_H: decode_float16,
    _FMT_BF: decode_bfloat16,
    _FMT_O3: decode_ofp8_e4m3,
    _FMT_O2: decode_ofp8_e5m2,
}


# ── Dispatcher functions ─────────────────────────────────────────


def float_to_bytes(
    value: float,
    fmt: int,
    rm: int = 0,
) -> tuple[bytes, FpExceptions]:
    """Encode a Python float to bytes in the given format.

    Args:
        value: The float to encode.
        fmt: Format code (0=F, 1=H, 2=BF, 3=O3, 4=O2).
        rm: Rounding mode (default RNE=0).

    Returns:
        (bytes_le, exceptions)
    """
    encoder = _ENCODERS.get(fmt)
    if encoder is None:
        raise ValueError(f"unsupported FP format code: {fmt}")
    return encoder(value, rm)


def bytes_to_float(data: bytes, fmt: int) -> float:
    """Decode bytes to Python float in the given format.

    Args:
        data: Raw bytes (LE).
        fmt: Format code (0=F, 1=H, 2=BF, 3=O3, 4=O2).

    Returns:
        Python float value.
    """
    width = _FMT_BYTES.get(fmt)
    if width is None:
        raise ValueError(f"unsupported FP format code: {fmt}")
    raw = data[:width]
    decoder = _DECODERS_RAW[fmt]
    return decoder(raw[0]) if width == 1 else decoder(raw)


# ── FP arithmetic helpers ────────────────────────────────────────


def _re_encode(
    result: float,
    fmt: int,
    rm: int,
) -> tuple[float, FpExceptions]:
    """Re-encode a float result through the target format.

    Detects overflow/underflow/inexact from the format's precision.
    """
    data, exc = float_to_bytes(result, fmt, rm)
    rt = bytes_to_float(data, fmt)
    return rt, exc


def _add_core(
    a: float,
    b: float,
    fmt: int,
    rm: int,
) -> tuple[float, FpExceptions]:
    """Add two floats, handling float64 absorption of tiny operands.

    When the exponent gap exceeds float64's 53-bit significand, ``a + b``
    returns the larger operand exactly.  For RNE this doesn't affect the
    final float32 value (both round to the same representable number), but
    for directed rounding we must nudge the float64 result so that
    ``_re_encode`` rounds in the correct direction.
    """
    result = a + b
    absorbed = False
    if not math.isinf(result):
        if a != 0.0 and result == b:
            absorbed = True
            # True sum is slightly shifted toward a's sign
            result = math.nextafter(b, math.copysign(math.inf, a))
        elif b != 0.0 and result == a:
            absorbed = True
            result = math.nextafter(a, math.copysign(math.inf, b))
    rt, exc = _re_encode(result, fmt, rm)
    if absorbed and not exc.inexact:
        exc = exc._replace(inexact=True)
    return rt, exc


def fp_add(
    a: float,
    b: float,
    fmt: int,
    rm: int = 0,
) -> tuple[float, FpExceptions]:
    """Perform a + b in the given FP format."""
    if math.isnan(a) or math.isnan(b):
        return float("nan"), FpExceptions(invalid=True)
    # Inf - Inf = NaN
    if math.isinf(a) and math.isinf(b) and a != b:
        return float("nan"), FpExceptions(invalid=True)
    return _add_core(a, b, fmt, rm)


def fp_sub(
    a: float,
    b: float,
    fmt: int,
    rm: int = 0,
) -> tuple[float, FpExceptions]:
    """Perform a - b in the given FP format."""
    if math.isnan(a) or math.isnan(b):
        return float("nan"), FpExceptions(invalid=True)
    # Inf - Inf = NaN
    if math.isinf(a) and math.isinf(b) and a == b:
        return float("nan"), FpExceptions(invalid=True)
    return _add_core(a, -b, fmt, rm)


def fp_mul(
    a: float,
    b: float,
    fmt: int,
    rm: int = 0,
) -> tuple[float, FpExceptions]:
    """Perform a * b in the given FP format."""
    if math.isnan(a) or math.isnan(b):
        return float("nan"), FpExceptions(invalid=True)
    # 0 * Inf or Inf * 0 = NaN
    if (a == 0.0 and math.isinf(b)) or (math.isinf(a) and b == 0.0):
        return float("nan"), FpExceptions(invalid=True)
    result = a * b
    return _re_encode(result, fmt, rm)


def fp_div(
    a: float,
    b: float,
    fmt: int,
    rm: int = 0,
) -> tuple[float, FpExceptions]:
    """Perform a / b in the given FP format."""
    if math.isnan(a) or math.isnan(b):
        return float("nan"), FpExceptions(invalid=True)
    # 0/0 = NaN (invalid)
    if a == 0.0 and b == 0.0:
        return float("nan"), FpExceptions(invalid=True)
    # Inf/Inf = NaN (invalid)
    if math.isinf(a) and math.isinf(b):
        return float("nan"), FpExceptions(invalid=True)
    # finite/0 = Inf (div_zero)
    if b == 0.0:
        sign = math.copysign(1.0, a) * math.copysign(1.0, b)
        return math.copysign(float("inf"), sign), FpExceptions(
            div_zero=True,
        )
    result = a / b
    return _re_encode(result, fmt, rm)


def fp_sqrt(
    value: float,
    fmt: int,
    rm: int = 0,
) -> tuple[float, FpExceptions]:
    """Compute sqrt(value) in the given FP format."""
    if math.isnan(value):
        return float("nan"), FpExceptions(invalid=True)
    if value < 0.0:
        return float("nan"), FpExceptions(invalid=True)
    if value == 0.0:
        return math.copysign(0.0, value), NO_EXC
    if math.isinf(value):
        return float("inf"), NO_EXC
    result = math.sqrt(value)
    return _re_encode(result, fmt, rm)


def fp_cmp(
    a: float,
    b: float,
) -> tuple[bool, bool, FpExceptions]:
    """Compare two floats, returning (zero_flag, carry_flag, exc).

    - a == b -> (True, False, ...)  [including +0 == -0]
    - a < b  -> (False, True, ...)
    - a > b  -> (False, False, ...)
    - Unordered (NaN) -> (True, True, ...)
    """
    if math.isnan(a) or math.isnan(b):
        return True, True, FpExceptions(invalid=True)
    if a == b:  # handles +0 == -0
        return True, False, NO_EXC
    if a < b:
        return False, True, NO_EXC
    return False, False, NO_EXC


def fp_abs(raw_bits: int, width: int) -> int:
    """Clear the sign bit. Pure bit manipulation."""
    sign_mask = 1 << (width - 1)
    return raw_bits & ~sign_mask


def fp_neg(raw_bits: int, width: int) -> int:
    """Toggle the sign bit. Pure bit manipulation."""
    sign_mask = 1 << (width - 1)
    return raw_bits ^ sign_mask


def fp_classify(
    value: float,
    raw_bits: int,
    width: int,
    fmt: int,
) -> int:
    """Return 8-bit classification bitmask per spec.

    Bits:
        0: ZERO (+/-0)
        1: SUB  (subnormal)
        2: NORM (normal finite)
        3: INF  (+/-Inf)
        4: QNAN (quiet NaN)
        5: SNAN (signaling NaN) -- not distinguishable in Python,
           so we always report qNaN for NaN inputs
        6: NEG  (sign bit set)
    """
    result = 0
    sign_mask = 1 << (width - 1)
    if raw_bits & sign_mask:
        result |= 0x40  # bit 6: NEG

    if math.isnan(value):
        result |= 0x10  # bit 4: QNAN
        return result

    if math.isinf(value):
        result |= 0x08  # bit 3: INF
        return result

    if value == 0.0:
        result |= 0x01  # bit 0: ZERO
        return result

    # Check subnormal by examining exponent bits
    if _is_subnormal(raw_bits, width, fmt):
        result |= 0x02  # bit 1: SUB
    else:
        result |= 0x04  # bit 2: NORM

    return result


_FMT_SHAPE: dict[int, tuple[int, int]] = {
    # fmt: (mant_bits, exp_bits)
    _FMT_F: (23, 8),
    _FMT_H: (10, 5),
    _FMT_BF: (7, 8),
    _FMT_O3: (3, 4),
    _FMT_O2: (2, 5),
}


def _is_subnormal(raw_bits: int, width: int, fmt: int) -> bool:
    """Check if the raw bits represent a subnormal number."""
    shape = _FMT_SHAPE.get(fmt)
    if shape is None:
        return False
    mant_bits, exp_bits = shape
    exp = (raw_bits >> mant_bits) & ((1 << exp_bits) - 1)
    mant = raw_bits & ((1 << mant_bits) - 1)
    return exp == 0 and mant != 0
