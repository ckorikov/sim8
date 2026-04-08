"""Unit tests for pysim8.sim.vu_ops — element-level VU arithmetic.

Covers:
- vu_read_elem: FP formats, uint8, int8 (signed conversion)
- vu_write_elem: FP path (bytes written + exceptions), integer path
- _arith_fp: all 6 ops (VADD/VSUB/VMUL/VDIV/VMAX/VMIN) including NaN handling
- _arith_uint8: all 6 ops + div-by-zero
- _arith_int8: all 6 ops + signed division + sign combinations
- vu_arith: dispatcher for FP / int8 / uint8
- vu_dot: dot product accumulation
- vu_sqrt: FP square root
- vu_neg: FP and integer negate (with overflow)
- vu_abs: FP, uint8, int8, int8=-128 edge
- vu_cmp + _compare: all 6 conditions for both FP and int, NaN paths
"""

from __future__ import annotations

import math
import struct

import pytest

from pysim8.fp_formats import FpExceptions, NO_EXC
from pysim8.isa import (
    Op,
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
)
from pysim8.sim.vu_ops import (
    vu_abs,
    vu_arith,
    vu_cmp,
    vu_dot,
    vu_neg,
    vu_read_elem,
    vu_sqrt,
    vu_write_elem,
)


# ── Helpers ───────────────────────────────────────────────────────


def mem(size: int = 64) -> bytearray:
    """Return a zeroed bytearray of the given size."""
    return bytearray(size)


def _pack_f32(val: float) -> bytes:
    return struct.pack("<f", val)


def _pack_f16(val: float) -> bytes:
    return struct.pack("<e", val)


def _f32_mem(val: float, offset: int = 0, size: int = 64) -> bytearray:
    """Return memory with a float32 value written at offset."""
    m = mem(size)
    raw = _pack_f32(val)
    for i, b in enumerate(raw):
        m[offset + i] = b
    return m


def _f16_mem(val: float, offset: int = 0, size: int = 64) -> bytearray:
    """Return memory with a float16 value written at offset."""
    m = mem(size)
    raw = _pack_f16(val)
    for i, b in enumerate(raw):
        m[offset + i] = b
    return m


# ── vu_read_elem ──────────────────────────────────────────────────


class TestVuReadElem:
    def test_read_float32(self) -> None:
        m = _f32_mem(3.14)
        result = vu_read_elem(m, 0, VU_FMT_F)
        assert isinstance(result, float)
        assert abs(result - 3.14) < 1e-5

    def test_read_float16(self) -> None:
        m = _f16_mem(1.5)
        result = vu_read_elem(m, 0, VU_FMT_H)
        assert isinstance(result, float)
        assert abs(result - 1.5) < 1e-3

    def test_read_bfloat16(self) -> None:
        # bfloat16 is top 2 bytes of float32; write them at addr
        raw_f32 = _pack_f32(2.0)
        m = mem()
        m[0] = raw_f32[2]  # bfloat16 LE = bytes [2] and [3] of float32
        m[1] = raw_f32[3]
        result = vu_read_elem(m, 0, VU_FMT_BF)
        assert isinstance(result, float)
        assert abs(result - 2.0) < 1e-2

    def test_read_ofp8_e4m3(self) -> None:
        m = mem()
        m[0] = 0x3C  # some valid OFP8 E4M3 value
        result = vu_read_elem(m, 0, VU_FMT_O3)
        assert isinstance(result, float)

    def test_read_ofp8_e5m2(self) -> None:
        m = mem()
        m[0] = 0x3C  # some valid OFP8 E5M2 value
        result = vu_read_elem(m, 0, VU_FMT_O2)
        assert isinstance(result, float)

    def test_read_uint8(self) -> None:
        m = mem()
        m[4] = 42
        result = vu_read_elem(m, 4, VU_FMT_U)
        assert result == 42

    def test_read_int8_positive(self) -> None:
        m = mem()
        m[0] = 100
        result = vu_read_elem(m, 0, VU_FMT_I)
        assert result == 100

    def test_read_int8_negative(self) -> None:
        # 0xFF = 255 unsigned → -1 signed
        m = mem()
        m[0] = 0xFF
        result = vu_read_elem(m, 0, VU_FMT_I)
        assert result == -1

    def test_read_int8_minus128(self) -> None:
        m = mem()
        m[0] = 0x80  # 128 unsigned → -128 signed
        result = vu_read_elem(m, 0, VU_FMT_I)
        assert result == -128

    def test_read_int8_boundary_127(self) -> None:
        m = mem()
        m[0] = 127
        result = vu_read_elem(m, 0, VU_FMT_I)
        assert result == 127

    def test_read_float32_at_offset(self) -> None:
        m = _f32_mem(7.0, offset=4)
        result = vu_read_elem(m, 4, VU_FMT_F)
        assert abs(result - 7.0) < 1e-5

    def test_read_uint8_zero(self) -> None:
        m = mem()
        result = vu_read_elem(m, 0, VU_FMT_U)
        assert result == 0

    def test_read_uint8_max(self) -> None:
        m = mem()
        m[0] = 255
        result = vu_read_elem(m, 0, VU_FMT_U)
        assert result == 255


# ── vu_write_elem ─────────────────────────────────────────────────


class TestVuWriteElem:
    def test_write_float32_basic(self) -> None:
        m = mem()
        exc = vu_write_elem(m, 0, VU_FMT_F, 1.0)
        assert isinstance(exc, FpExceptions)
        result = struct.unpack("<f", bytes(m[0:4]))[0]
        assert abs(result - 1.0) < 1e-7

    def test_write_float32_returns_exceptions(self) -> None:
        m = mem()
        exc = vu_write_elem(m, 0, VU_FMT_F, 1.5)
        # No exceptions for a normal representable value
        assert not exc.overflow
        assert not exc.underflow

    def test_write_float16(self) -> None:
        m = mem()
        exc = vu_write_elem(m, 0, VU_FMT_H, 2.0)
        assert isinstance(exc, FpExceptions)
        result = struct.unpack("<e", bytes(m[0:2]))[0]
        assert abs(result - 2.0) < 1e-3

    def test_write_bfloat16(self) -> None:
        m = mem()
        exc = vu_write_elem(m, 0, VU_FMT_BF, 1.0)
        assert isinstance(exc, FpExceptions)
        assert VU_FMT_ELEM_SIZE[VU_FMT_BF] == 2

    def test_write_uint8_basic(self) -> None:
        m = mem()
        exc = vu_write_elem(m, 0, VU_FMT_U, 200)
        assert exc == FpExceptions()
        assert m[0] == 200

    def test_write_uint8_wraps(self) -> None:
        m = mem()
        vu_write_elem(m, 0, VU_FMT_U, 257)
        assert m[0] == 1  # 257 & 0xFF

    def test_write_int8(self) -> None:
        m = mem()
        vu_write_elem(m, 0, VU_FMT_I, -1)
        assert m[0] == 0xFF

    def test_write_float32_at_offset(self) -> None:
        m = mem()
        vu_write_elem(m, 4, VU_FMT_F, 5.0)
        result = struct.unpack("<f", bytes(m[4:8]))[0]
        assert abs(result - 5.0) < 1e-7

    def test_write_fp_bytes_count(self) -> None:
        """float32 must write exactly 4 bytes."""
        m = mem()
        vu_write_elem(m, 0, VU_FMT_F, 1.0)
        # bytes 0-3 should be non-zero for 1.0 (IEEE 754: 0x3F800000)
        assert bytes(m[0:4]) == b"\x00\x00\x80\x3f"

    def test_write_ofp8_e4m3(self) -> None:
        m = mem()
        exc = vu_write_elem(m, 0, VU_FMT_O3, 1.0)
        assert isinstance(exc, FpExceptions)
        assert VU_FMT_ELEM_SIZE[VU_FMT_O3] == 1

    def test_write_ofp8_e5m2(self) -> None:
        m = mem()
        exc = vu_write_elem(m, 0, VU_FMT_O2, 1.0)
        assert isinstance(exc, FpExceptions)


# ── _arith_fp (via vu_arith) ──────────────────────────────────────


class TestArithFP:
    @pytest.mark.parametrize(
        "op,a,b,expected",
        [
            pytest.param(Op.VADD, 1.0, 2.0, 3.0, id="vadd"),
            pytest.param(Op.VSUB, 5.0, 3.0, 2.0, id="vsub"),
            pytest.param(Op.VMUL, 3.0, 4.0, 12.0, id="vmul"),
            pytest.param(Op.VDIV, 10.0, 2.0, 5.0, id="vdiv"),
            pytest.param(Op.VMAX, 3.0, 5.0, 5.0, id="vmax_normal"),
            pytest.param(Op.VMIN, 3.0, 5.0, 3.0, id="vmin_normal"),
        ],
    )
    def test_fp_basic(self, op: Op, a: float, b: float, expected: float) -> None:
        result, exc = vu_arith(int(op), a, b, VU_FMT_F)
        assert abs(result - expected) < 1e-5  # type: ignore[arg-type]
        assert isinstance(exc, FpExceptions)

    def test_vmax_nan_a(self) -> None:
        # When a is NaN, vmax returns b
        result, exc = vu_arith(int(Op.VMAX), float("nan"), 3.0, VU_FMT_F)
        assert result == 3.0
        assert exc == NO_EXC

    def test_vmax_nan_b(self) -> None:
        # When b is NaN (a is not NaN), vmax returns a
        result, exc = vu_arith(int(Op.VMAX), 3.0, float("nan"), VU_FMT_F)
        assert result == 3.0
        assert exc == NO_EXC

    def test_vmin_nan_a(self) -> None:
        result, exc = vu_arith(int(Op.VMIN), float("nan"), 3.0, VU_FMT_F)
        assert result == 3.0
        assert exc == NO_EXC

    def test_vmin_nan_b(self) -> None:
        result, exc = vu_arith(int(Op.VMIN), 3.0, float("nan"), VU_FMT_F)
        assert result == 3.0
        assert exc == NO_EXC

    def test_fp_float16(self) -> None:
        result, exc = vu_arith(int(Op.VADD), 1.0, 1.0, VU_FMT_H)
        assert abs(result - 2.0) < 1e-3  # type: ignore[arg-type]

    def test_fp_bfloat16(self) -> None:
        result, exc = vu_arith(int(Op.VMUL), 2.0, 3.0, VU_FMT_BF)
        assert abs(result - 6.0) < 0.1  # type: ignore[arg-type]

    def test_unknown_fp_op_raises(self) -> None:
        # Op code 0 is HLT — not a VU FP op
        with pytest.raises(ValueError, match="Unknown FP VU op"):
            vu_arith(0, 1.0, 2.0, VU_FMT_F)


# ── _arith_uint8 (via vu_arith) ───────────────────────────────────


class TestArithUint8:
    @pytest.mark.parametrize(
        "op,a,b,expected_val",
        [
            pytest.param(Op.VADD, 10, 20, 30, id="vadd"),
            pytest.param(Op.VSUB, 30, 10, 20, id="vsub"),
            pytest.param(Op.VMUL, 5, 6, 30, id="vmul"),
            pytest.param(Op.VDIV, 20, 4, 5, id="vdiv"),
            pytest.param(Op.VMAX, 10, 30, 30, id="vmax"),
            pytest.param(Op.VMIN, 10, 30, 10, id="vmin"),
        ],
    )
    def test_basic(self, op: Op, a: int, b: int, expected_val: int) -> None:
        result, exc = vu_arith(int(op), a, b, VU_FMT_U)
        assert result == expected_val
        assert isinstance(exc, FpExceptions)

    def test_add_wraps_with_overflow_exc(self) -> None:
        result, exc = vu_arith(int(Op.VADD), 200, 100, VU_FMT_U)
        assert result == 44  # (200 + 100) & 0xFF
        assert exc.overflow

    def test_sub_underflow_exc(self) -> None:
        result, exc = vu_arith(int(Op.VSUB), 5, 10, VU_FMT_U)
        assert result == (5 - 10) & 0xFF
        assert exc.underflow

    def test_mul_overflow(self) -> None:
        result, exc = vu_arith(int(Op.VMUL), 200, 2, VU_FMT_U)
        assert result == (200 * 2) & 0xFF
        assert exc.overflow

    def test_div_by_zero_returns_zero(self) -> None:
        result, exc = vu_arith(int(Op.VDIV), 10, 0, VU_FMT_U)
        assert result == 0
        assert exc == NO_EXC

    def test_div_normal(self) -> None:
        result, exc = vu_arith(int(Op.VDIV), 10, 3, VU_FMT_U)
        assert result == 3  # floor division

    def test_unknown_uint8_op_raises(self) -> None:
        with pytest.raises(ValueError, match="Unknown UINT8 VU op"):
            vu_arith(0, 1, 2, VU_FMT_U)


# ── _arith_int8 (via vu_arith) ────────────────────────────────────


class TestArithInt8:
    @pytest.mark.parametrize(
        "op,a,b,expected_val",
        [
            pytest.param(Op.VADD, 10, 20, 30, id="vadd_pos"),
            pytest.param(Op.VSUB, 10, 5, 5, id="vsub_pos"),
            pytest.param(Op.VMUL, 3, 4, 12, id="vmul_pos"),
            pytest.param(Op.VDIV, 10, 3, 3, id="vdiv_truncate"),
            # VMAX/VMIN for int8 return raw signed ints (not byte-wrapped)
            pytest.param(Op.VMAX, -5, 3, 3, id="vmax"),
            pytest.param(Op.VMIN, -5, 3, -5, id="vmin"),
        ],
    )
    def test_basic(self, op: Op, a: int, b: int, expected_val: int) -> None:
        result, exc = vu_arith(int(op), a, b, VU_FMT_I)
        assert result == expected_val
        assert isinstance(exc, FpExceptions)

    def test_add_large_no_byte_overflow(self) -> None:
        # raw = 100 + 50 = 150; _int_exc checks raw > 255 for overflow
        # 150 is not > 255, so no overflow flag
        result, exc = vu_arith(int(Op.VADD), 100, 50, VU_FMT_I)
        assert result == 150 & 0xFF
        assert not exc.overflow

    def test_add_wraps_when_sum_over_255(self) -> None:
        # raw = 200 + 100 = 300 > 255 → overflow flag set
        result, exc = vu_arith(int(Op.VADD), 200, 100, VU_FMT_I)
        assert result == 300 & 0xFF
        assert exc.overflow

    def test_sub_underflow(self) -> None:
        result, exc = vu_arith(int(Op.VSUB), -100, 50, VU_FMT_I)
        raw = -100 - 50  # = -150
        assert result == raw & 0xFF
        assert exc.underflow

    def test_div_by_zero_returns_zero(self) -> None:
        result, exc = vu_arith(int(Op.VDIV), 10, 0, VU_FMT_I)
        assert result == 0
        assert exc == NO_EXC

    def test_div_negative_positive(self) -> None:
        # -10 / 3 → sign=-1, abs(10)//3 = 3, result = -3 → 0xFD
        result, exc = vu_arith(int(Op.VDIV), -10, 3, VU_FMT_I)
        assert result == (-3) & 0xFF

    def test_div_positive_negative(self) -> None:
        # 10 / -3 → sign=-1, result = -3 → 0xFD
        result, exc = vu_arith(int(Op.VDIV), 10, -3, VU_FMT_I)
        assert result == (-3) & 0xFF

    def test_div_negative_negative(self) -> None:
        # -10 / -3 → sign=1, result = 3
        result, exc = vu_arith(int(Op.VDIV), -10, -3, VU_FMT_I)
        assert result == 3

    def test_vmax_both_negative(self) -> None:
        # VMAX returns raw signed int (not byte-wrapped)
        result, exc = vu_arith(int(Op.VMAX), -10, -5, VU_FMT_I)
        assert result == -5  # -5 > -10

    def test_vmin_both_negative(self) -> None:
        # VMIN returns raw signed int (not byte-wrapped)
        result, exc = vu_arith(int(Op.VMIN), -10, -5, VU_FMT_I)
        assert result == -10  # -10 < -5

    def test_unknown_int8_op_raises(self) -> None:
        with pytest.raises(ValueError, match="Unknown INT8 VU op"):
            vu_arith(0, 1, 2, VU_FMT_I)


# ── vu_arith dispatcher ───────────────────────────────────────────


class TestVuArithDispatch:
    def test_dispatches_to_fp(self) -> None:
        result, exc = vu_arith(int(Op.VADD), 1.0, 2.0, VU_FMT_F)
        assert abs(result - 3.0) < 1e-5  # type: ignore[arg-type]

    def test_dispatches_to_int8(self) -> None:
        result, exc = vu_arith(int(Op.VADD), 10, 20, VU_FMT_I)
        assert result == 30

    def test_dispatches_to_uint8(self) -> None:
        result, exc = vu_arith(int(Op.VADD), 10, 20, VU_FMT_U)
        assert result == 30

    @pytest.mark.parametrize(
        "fmt",
        [
            pytest.param(VU_FMT_F, id="float32"),
            pytest.param(VU_FMT_H, id="float16"),
            pytest.param(VU_FMT_BF, id="bfloat16"),
            pytest.param(VU_FMT_O3, id="ofp8_e4m3"),
            pytest.param(VU_FMT_O2, id="ofp8_e5m2"),
        ],
    )
    def test_fp_formats_dispatch(self, fmt: int) -> None:
        result, exc = vu_arith(int(Op.VADD), 1.0, 1.0, fmt)
        assert isinstance(result, float)
        assert isinstance(exc, FpExceptions)


# ── vu_dot ────────────────────────────────────────────────────────


class TestVuDot:
    def test_basic(self) -> None:
        result = vu_dot([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])
        assert abs(result - 32.0) < 1e-5  # 4 + 10 + 18

    def test_empty(self) -> None:
        result = vu_dot([], [])
        assert result == 0.0

    def test_single(self) -> None:
        result = vu_dot([3.0], [4.0])
        assert abs(result - 12.0) < 1e-5

    def test_with_zeros(self) -> None:
        result = vu_dot([1.0, 0.0, 2.0], [0.0, 5.0, 3.0])
        assert abs(result - 6.0) < 1e-5

    def test_accumulates_left_to_right(self) -> None:
        # Just verify correct sum for a longer vector
        a = [1.0, 2.0, 3.0, 4.0]
        b = [1.0, 1.0, 1.0, 1.0]
        result = vu_dot(a, b)
        assert abs(result - 10.0) < 1e-5


# ── vu_sqrt ───────────────────────────────────────────────────────


class TestVuSqrt:
    def test_sqrt_4(self) -> None:
        result, exc = vu_sqrt(4.0, VU_FMT_F)
        assert abs(result - 2.0) < 1e-5  # type: ignore[arg-type]
        assert isinstance(exc, FpExceptions)

    def test_sqrt_9(self) -> None:
        result, exc = vu_sqrt(9.0, VU_FMT_F)
        assert abs(result - 3.0) < 1e-5  # type: ignore[arg-type]

    def test_sqrt_zero(self) -> None:
        result, exc = vu_sqrt(0.0, VU_FMT_F)
        assert result == 0.0  # type: ignore[arg-type]

    def test_sqrt_float16(self) -> None:
        result, exc = vu_sqrt(4.0, VU_FMT_H)
        assert abs(result - 2.0) < 1e-2  # type: ignore[arg-type]

    def test_sqrt_int_input_coerced(self) -> None:
        # vu_sqrt calls float(val) internally
        result, exc = vu_sqrt(16, VU_FMT_F)
        assert abs(result - 4.0) < 1e-5  # type: ignore[arg-type]


# ── vu_neg ────────────────────────────────────────────────────────


class TestVuNeg:
    def test_neg_fp_positive(self) -> None:
        result, exc = vu_neg(3.0, VU_FMT_F)
        assert result == -3.0
        assert exc == NO_EXC

    def test_neg_fp_negative(self) -> None:
        result, exc = vu_neg(-5.0, VU_FMT_F)
        assert result == 5.0
        assert exc == NO_EXC

    def test_neg_fp_zero(self) -> None:
        result, exc = vu_neg(0.0, VU_FMT_F)
        assert result == 0.0 or result == -0.0

    def test_neg_fp_float16(self) -> None:
        result, exc = vu_neg(2.0, VU_FMT_H)
        assert result == -2.0
        assert exc == NO_EXC

    def test_neg_uint8_positive(self) -> None:
        # neg(10) → raw=-10 → 0xF6=246, underflow
        result, exc = vu_neg(10, VU_FMT_U)
        assert result == (-10) & 0xFF
        assert exc.underflow

    def test_neg_uint8_zero(self) -> None:
        result, exc = vu_neg(0, VU_FMT_U)
        assert result == 0
        assert not exc.underflow

    def test_neg_int8_positive(self) -> None:
        result, exc = vu_neg(5, VU_FMT_I)
        assert result == (-5) & 0xFF
        assert exc.underflow

    def test_neg_int8_negative(self) -> None:
        # neg(-5) → raw=5 → no exception
        result, exc = vu_neg(-5, VU_FMT_I)
        assert result == 5
        assert not exc.underflow


# ── vu_abs ────────────────────────────────────────────────────────


class TestVuAbs:
    def test_abs_fp_positive(self) -> None:
        result, exc = vu_abs(3.0, VU_FMT_F)
        assert result == 3.0
        assert isinstance(exc, FpExceptions)

    def test_abs_fp_negative(self) -> None:
        result, exc = vu_abs(-5.0, VU_FMT_F)
        assert result == 5.0

    def test_abs_fp_zero(self) -> None:
        result, exc = vu_abs(0.0, VU_FMT_F)
        assert result == 0.0

    def test_abs_fp_float16(self) -> None:
        result, exc = vu_abs(-2.0, VU_FMT_H)
        assert result == 2.0

    def test_abs_fp_bfloat16(self) -> None:
        result, exc = vu_abs(-1.0, VU_FMT_BF)
        assert result == 1.0

    def test_abs_uint8_basic(self) -> None:
        result, exc = vu_abs(42, VU_FMT_U)
        assert result == 42
        assert isinstance(exc, FpExceptions)

    def test_abs_uint8_max(self) -> None:
        result, exc = vu_abs(255, VU_FMT_U)
        assert result == 255

    def test_abs_int8_negative(self) -> None:
        result, exc = vu_abs(-5, VU_FMT_I)
        assert result == 5

    def test_abs_int8_positive(self) -> None:
        result, exc = vu_abs(5, VU_FMT_I)
        assert result == 5

    def test_abs_int8_minus128_edge(self) -> None:
        # -128 has no positive counterpart in int8; returns wrapped 0x80
        result, exc = vu_abs(-128, VU_FMT_I)
        assert result == 0x80  # 128 (wraps back to -128 in int8)
        assert isinstance(exc, FpExceptions)


# ── vu_cmp ────────────────────────────────────────────────────────


class TestVuCmp:
    @pytest.mark.parametrize(
        "a,b,cond,expected",
        [
            pytest.param(1.0, 1.0, VU_CMP_EQ, 0xFF, id="fp_eq_true"),
            pytest.param(1.0, 2.0, VU_CMP_EQ, 0x00, id="fp_eq_false"),
            pytest.param(1.0, 2.0, VU_CMP_NE, 0xFF, id="fp_ne_true"),
            pytest.param(1.0, 1.0, VU_CMP_NE, 0x00, id="fp_ne_false"),
            pytest.param(1.0, 2.0, VU_CMP_LT, 0xFF, id="fp_lt_true"),
            pytest.param(2.0, 1.0, VU_CMP_LT, 0x00, id="fp_lt_false"),
            pytest.param(1.0, 2.0, VU_CMP_LE, 0xFF, id="fp_le_lt"),
            pytest.param(1.0, 1.0, VU_CMP_LE, 0xFF, id="fp_le_eq"),
            pytest.param(2.0, 1.0, VU_CMP_LE, 0x00, id="fp_le_false"),
            pytest.param(2.0, 1.0, VU_CMP_GT, 0xFF, id="fp_gt_true"),
            pytest.param(1.0, 2.0, VU_CMP_GT, 0x00, id="fp_gt_false"),
            pytest.param(2.0, 1.0, VU_CMP_GE, 0xFF, id="fp_ge_gt"),
            pytest.param(1.0, 1.0, VU_CMP_GE, 0xFF, id="fp_ge_eq"),
            pytest.param(1.0, 2.0, VU_CMP_GE, 0x00, id="fp_ge_false"),
        ],
    )
    def test_fp_conditions(self, a: float, b: float, cond: int, expected: int) -> None:
        result = vu_cmp(a, b, cond, VU_FMT_F)
        assert result == expected

    def test_fp_nan_ne_returns_true(self) -> None:
        # NaN comparison: NE returns 0xFF
        result = vu_cmp(float("nan"), 1.0, VU_CMP_NE, VU_FMT_F)
        assert result == 0xFF

    def test_fp_nan_eq_returns_false(self) -> None:
        # NaN comparison: EQ returns 0x00
        result = vu_cmp(float("nan"), float("nan"), VU_CMP_EQ, VU_FMT_F)
        assert result == 0x00

    def test_fp_nan_b_ne_returns_true(self) -> None:
        result = vu_cmp(1.0, float("nan"), VU_CMP_NE, VU_FMT_F)
        assert result == 0xFF

    def test_fp_nan_lt_returns_false(self) -> None:
        result = vu_cmp(float("nan"), 1.0, VU_CMP_LT, VU_FMT_F)
        assert result == 0x00

    @pytest.mark.parametrize(
        "a,b,cond,expected",
        [
            pytest.param(5, 5, VU_CMP_EQ, 0xFF, id="int_eq_true"),
            pytest.param(5, 6, VU_CMP_EQ, 0x00, id="int_eq_false"),
            pytest.param(5, 6, VU_CMP_NE, 0xFF, id="int_ne_true"),
            pytest.param(5, 5, VU_CMP_NE, 0x00, id="int_ne_false"),
            pytest.param(3, 5, VU_CMP_LT, 0xFF, id="int_lt_true"),
            pytest.param(5, 3, VU_CMP_LT, 0x00, id="int_lt_false"),
            pytest.param(3, 5, VU_CMP_LE, 0xFF, id="int_le_lt"),
            pytest.param(5, 5, VU_CMP_LE, 0xFF, id="int_le_eq"),
            pytest.param(6, 5, VU_CMP_LE, 0x00, id="int_le_false"),
            pytest.param(6, 5, VU_CMP_GT, 0xFF, id="int_gt_true"),
            pytest.param(5, 6, VU_CMP_GT, 0x00, id="int_gt_false"),
            pytest.param(6, 5, VU_CMP_GE, 0xFF, id="int_ge_gt"),
            pytest.param(5, 5, VU_CMP_GE, 0xFF, id="int_ge_eq"),
            pytest.param(5, 6, VU_CMP_GE, 0x00, id="int_ge_false"),
        ],
    )
    def test_int_conditions(self, a: int, b: int, cond: int, expected: int) -> None:
        result = vu_cmp(a, b, cond, VU_FMT_U)
        assert result == expected

    def test_int8_cmp_eq(self) -> None:
        result = vu_cmp(-5, -5, VU_CMP_EQ, VU_FMT_I)
        assert result == 0xFF

    def test_unknown_cond_raises(self) -> None:
        from pysim8.sim.vu_ops import _compare  # type: ignore[attr-defined]

        with pytest.raises(ValueError, match="Unknown VU comparison condition"):
            _compare(1, 2, 99)
