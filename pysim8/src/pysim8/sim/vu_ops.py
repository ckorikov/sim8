"""VU element-level arithmetic operations.

Each function operates on single elements (Python floats for FP, ints for integer).
The VU executor calls these per-element in a loop.
"""

from __future__ import annotations

import math
from typing import TYPE_CHECKING

from pysim8.fp_formats import (
    NO_EXC,
    FpExceptions,
    bytes_to_float,
    float_to_bytes,
    fp_add,
    fp_div,
    fp_mul,
    fp_sub,
)
from pysim8.fp_formats import (
    fp_sqrt as _fp_sqrt,
)
from pysim8.isa import (
    VU_CMP_EQ,
    VU_CMP_GE,
    VU_CMP_GT,
    VU_CMP_LE,
    VU_CMP_LT,
    VU_CMP_NE,
    VU_FMT_BF,
    VU_FMT_ELEM_SIZE,
    VU_FMT_F,
    VU_FMT_H,
    VU_FMT_I,
    VU_FMT_O2,
    VU_FMT_O3,
    VU_FMT_U,
    Op,
)

if TYPE_CHECKING:
    from .memory import Memory

__all__ = [
    "vu_read_elem",
    "vu_write_elem",
    "vu_arith",
    "vu_dot",
    "vu_sqrt",
    "vu_neg",
    "vu_abs",
    "vu_cmp",
]

_FP_FMTS = frozenset({VU_FMT_F, VU_FMT_H, VU_FMT_BF, VU_FMT_O3, VU_FMT_O2})


def _to_byte(val: int) -> int:
    """Wrap integer to unsigned byte (mod 256)."""
    return val & 0xFF


def vu_read_elem(mem: Memory, addr: int, fmt: int) -> float | int:
    """Read one element from memory at addr in the given format."""
    sz = VU_FMT_ELEM_SIZE[fmt]
    raw = bytes(mem[addr + i] for i in range(sz))
    if fmt in _FP_FMTS:
        return bytes_to_float(raw, fmt)
    val = int.from_bytes(raw, "little")
    if fmt == VU_FMT_I:
        return val if val < 128 else val - 256
    return val


def vu_write_elem(mem: Memory, addr: int, fmt: int, val: float | int, rm: int = 0) -> FpExceptions:
    """Write one element to memory. Returns FP exceptions (empty for integer)."""
    sz = VU_FMT_ELEM_SIZE[fmt]
    if fmt in _FP_FMTS:
        raw, exc = float_to_bytes(float(val), fmt, rm)
        for i in range(sz):
            mem[addr + i] = raw[i]
        return exc
    mem[addr] = int(val) & 0xFF
    return FpExceptions()


def _arith_fp(op: int, a: float, b: float, fmt: int, rm: int = 0) -> tuple[float, FpExceptions]:
    if op == Op.VADD:
        return fp_add(a, b, fmt, rm)
    if op == Op.VSUB:
        return fp_sub(a, b, fmt, rm)
    if op == Op.VMUL:
        return fp_mul(a, b, fmt, rm)
    if op == Op.VDIV:
        return fp_div(a, b, fmt, rm)
    if op == Op.VMAX:
        val = b if math.isnan(a) else (a if math.isnan(b) else max(a, b))
        return val, NO_EXC
    if op == Op.VMIN:
        val = b if math.isnan(a) else (a if math.isnan(b) else min(a, b))
        return val, NO_EXC
    raise ValueError(f"Unknown FP VU op: {op}")


def _int_exc(raw: int) -> FpExceptions:
    """Return overflow/underflow exceptions for integer result before wrapping."""
    return FpExceptions(overflow=raw > 255, underflow=raw < 0)


def _arith_uint8(op: int, a: int, b: int) -> tuple[int, FpExceptions]:
    ua, ub = a & 0xFF, b & 0xFF
    if op == Op.VADD:
        raw = ua + ub
        return _to_byte(raw), _int_exc(raw)
    if op == Op.VSUB:
        raw = ua - ub
        return _to_byte(raw), _int_exc(raw)
    if op == Op.VMUL:
        raw = ua * ub
        return _to_byte(raw), _int_exc(raw)
    if op == Op.VDIV:
        return (0, NO_EXC) if ub == 0 else (ua // ub, NO_EXC)
    if op == Op.VMAX:
        return max(ua, ub), NO_EXC
    if op == Op.VMIN:
        return min(ua, ub), NO_EXC
    raise ValueError(f"Unknown UINT8 VU op: {op}")


def _arith_int8(op: int, a: int, b: int) -> tuple[int, FpExceptions]:
    if op == Op.VADD:
        raw = a + b
        return _to_byte(raw), _int_exc(raw)
    if op == Op.VSUB:
        raw = a - b
        return _to_byte(raw), _int_exc(raw)
    if op == Op.VMUL:
        raw = a * b
        return _to_byte(raw), _int_exc(raw)
    if op == Op.VDIV:
        if b == 0:
            return 0, NO_EXC
        sign = -1 if (a < 0) ^ (b < 0) else 1
        return _to_byte(sign * (abs(a) // abs(b))), NO_EXC
    if op == Op.VMAX:
        return (a if a >= b else b), NO_EXC
    if op == Op.VMIN:
        return (a if a <= b else b), NO_EXC
    raise ValueError(f"Unknown INT8 VU op: {op}")


def vu_arith(
    op: int,
    a: float | int,
    b: float | int,
    fmt: int,
    rm: int = 0,
) -> tuple[float | int, FpExceptions]:
    """Elementwise binary arithmetic. Returns (result, exceptions)."""
    if fmt in _FP_FMTS:
        return _arith_fp(op, float(a), float(b), fmt, rm)
    if fmt == VU_FMT_I:
        return _arith_int8(op, int(a), int(b))
    return _arith_uint8(op, int(a), int(b))


def vu_dot(values_a: list[float], values_b: list[float]) -> float:
    """Compute dot product (FP only). Left-to-right accumulation."""
    acc = 0.0
    for a, b in zip(values_a, values_b):
        acc += a * b
    return acc


def vu_sqrt(val: float | int, fmt: int, rm: int = 0) -> tuple[float | int, FpExceptions]:
    """Element square root (FP only — caller validates format)."""
    return _fp_sqrt(float(val), fmt, rm)


def vu_neg(val: float | int, fmt: int) -> tuple[float | int, FpExceptions]:
    """Element negate."""
    if fmt in _FP_FMTS:
        return -float(val), NO_EXC
    raw = -int(val)
    return raw & 0xFF, _int_exc(raw)


def vu_abs(val: float | int, fmt: int) -> tuple[float | int, FpExceptions]:
    """Element absolute value."""
    if fmt in _FP_FMTS:
        return abs(float(val)), FpExceptions()
    if fmt == VU_FMT_U:
        return int(val) & 0xFF, FpExceptions()
    iv = int(val)
    if iv == -128:
        return _to_byte(-128), FpExceptions()
    return _to_byte(abs(iv)), FpExceptions()


def vu_cmp(a: float | int, b: float | int, cond: int, fmt: int) -> int:
    """Compare two elements. Returns 0xFF (true) or 0x00 (false)."""
    if fmt in _FP_FMTS:
        fa, fb = float(a), float(b)
        if math.isnan(fa) or math.isnan(fb):
            return 0xFF if cond == VU_CMP_NE else 0x00
        result = _compare(fa, fb, cond)
    else:
        result = _compare(a, b, cond)
    return 0xFF if result else 0x00


def _compare(a: float | int, b: float | int, cond: int) -> bool:
    if cond == VU_CMP_EQ:
        return a == b
    if cond == VU_CMP_NE:
        return a != b
    if cond == VU_CMP_LT:
        return a < b
    if cond == VU_CMP_LE:
        return a <= b
    if cond == VU_CMP_GT:
        return a > b
    if cond == VU_CMP_GE:
        return a >= b
    raise ValueError(f"Unknown VU comparison condition: {cond}")
