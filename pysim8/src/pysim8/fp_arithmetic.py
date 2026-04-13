"""FP arithmetic operations for sim8 formats."""

from __future__ import annotations

import math

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
from pysim8.fp_formats import (
    NO_EXC,
    FpExceptions,
    bytes_to_float,
    float_to_bytes,
)

_NAN_INVALID: tuple[float, FpExceptions] = (float("nan"), FpExceptions(invalid=True))

__all__ = [
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

_FMT_SHAPE: dict[int, tuple[int, int]] = {
    # fmt: (mant_bits, exp_bits)
    _FMT_F: (23, 8),
    _FMT_H: (10, 5),
    _FMT_BF: (7, 8),
    _FMT_O3: (3, 4),
    _FMT_O2: (2, 5),
}


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
        return _NAN_INVALID
    # Inf - Inf = NaN
    if math.isinf(a) and math.isinf(b) and a != b:
        return _NAN_INVALID
    return _add_core(a, b, fmt, rm)


def fp_sub(
    a: float,
    b: float,
    fmt: int,
    rm: int = 0,
) -> tuple[float, FpExceptions]:
    """Perform a - b in the given FP format."""
    if math.isnan(a) or math.isnan(b):
        return _NAN_INVALID
    # Inf - Inf = NaN
    if math.isinf(a) and math.isinf(b) and a == b:
        return _NAN_INVALID
    return _add_core(a, -b, fmt, rm)


def fp_mul(
    a: float,
    b: float,
    fmt: int,
    rm: int = 0,
) -> tuple[float, FpExceptions]:
    """Perform a * b in the given FP format."""
    if math.isnan(a) or math.isnan(b):
        return _NAN_INVALID
    # 0 * Inf or Inf * 0 = NaN
    if (a == 0.0 and math.isinf(b)) or (math.isinf(a) and b == 0.0):
        return _NAN_INVALID
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
        return _NAN_INVALID
    # 0/0 = NaN (invalid)
    if a == 0.0 and b == 0.0:
        return _NAN_INVALID
    # Inf/Inf = NaN (invalid)
    if math.isinf(a) and math.isinf(b):
        return _NAN_INVALID
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
    if math.isnan(value) or value < 0.0:
        return _NAN_INVALID
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


def _is_subnormal(raw_bits: int, width: int, fmt: int) -> bool:
    """Check if the raw bits represent a subnormal number."""
    shape = _FMT_SHAPE.get(fmt)
    if shape is None:
        return False
    mant_bits, exp_bits = shape
    exp = (raw_bits >> mant_bits) & ((1 << exp_bits) - 1)
    mant = raw_bits & ((1 << mant_bits) - 1)
    return exp == 0 and mant != 0


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
