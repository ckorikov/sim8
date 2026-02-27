"""Cross-validate OFP8 E4M3 / E5M2 against ml_dtypes + OFP8 spec.

ml_dtypes (jax-ml/ml_dtypes) is the reference NumPy implementation of
8-bit float types from the OCP MX spec.  We use it as an oracle to
verify that our pure-Python encode/decode and arithmetic in fp_formats.py
are bit-exact.

ml_dtypes is a *dev-only* dependency; these tests are skipped gracefully
when the package is not installed.

OFP8 spec reference: OCP 8-bit Floating Point Specification (OFP8)
Revision 1.0, 2023-12-01.  Section 5.2.1, Table 3 defines two conversion
modes:

  - SAT (saturating): overflow → ±max_finite
  - NONSAT (non-saturating): overflow → NaN (E4M3) or ±Inf (E5M2)

Our sim8 implementation:
  - E4M3: SAT mode  (no Inf representation; overflow → max_finite)
  - E5M2: IEEE 754 standard (overflow → ±Inf) = NONSAT mode

ml_dtypes float8_e4m3fn uses NONSAT mode (overflow → NaN), so E4M3
overflow cases are expected to diverge and are skipped.
"""

from __future__ import annotations

import math
import struct

import pytest

np = pytest.importorskip("numpy")
ml_dtypes = pytest.importorskip("ml_dtypes")

from pysim8.fp_formats import (
    RoundingMode,
    decode_ofp8_e4m3,
    decode_ofp8_e5m2,
    encode_ofp8_e4m3,
    encode_ofp8_e5m2,
    fp_add,
    fp_sub,
    fp_mul,
    fp_div,
    fp_sqrt,
)

# ml_dtypes scalar types
E4M3 = ml_dtypes.float8_e4m3fn
E5M2 = ml_dtypes.float8_e5m2


# ── helpers ──────────────────────────────────────────────────────────────


def _ml_decode_e4m3(byte_val: int) -> float:
    """Decode one byte as E4M3 via ml_dtypes."""
    arr = np.frombuffer(bytes([byte_val]), dtype=E4M3)
    return float(arr[0])


def _ml_decode_e5m2(byte_val: int) -> float:
    """Decode one byte as E5M2 via ml_dtypes."""
    arr = np.frombuffer(bytes([byte_val]), dtype=E5M2)
    return float(arr[0])


def _ml_encode_e4m3(value: float) -> int:
    """Encode a float as E4M3 via ml_dtypes (RNE only)."""
    arr = np.array([value], dtype=np.float32).astype(E4M3)
    return int(arr.view(np.uint8)[0])


def _ml_encode_e5m2(value: float) -> int:
    """Encode a float as E5M2 via ml_dtypes (RNE only)."""
    arr = np.array([value], dtype=np.float32).astype(E5M2)
    return int(arr.view(np.uint8)[0])


def _same_float(a: float, b: float) -> bool:
    """Compare two floats, treating NaN == NaN and +0 == -0."""
    if math.isnan(a) and math.isnan(b):
        return True
    if a == 0.0 and b == 0.0:
        # We don't check sign of zero: ml_dtypes may differ on -0 NaN sign
        return True
    return a == b


def _same_float_strict(a: float, b: float) -> bool:
    """Compare two floats, treating NaN == NaN but distinguishing +0/-0."""
    if math.isnan(a) and math.isnan(b):
        return True
    if a == 0.0 and b == 0.0:
        return math.copysign(1.0, a) == math.copysign(1.0, b)
    return a == b


# ── E4M3: exhaustive decode (all 256 byte values) ───────────────────────


class TestE4M3Decode:
    """Verify decode_ofp8_e4m3 matches ml_dtypes for all 256 patterns."""

    @pytest.mark.parametrize("byte_val", range(256))
    def test_decode_all(self, byte_val: int) -> None:
        ours = decode_ofp8_e4m3(byte_val)
        ref = _ml_decode_e4m3(byte_val)
        assert _same_float(ours, ref), (
            f"E4M3 decode mismatch for 0x{byte_val:02X}: "
            f"ours={ours!r}, ml_dtypes={ref!r}"
        )


# ── E5M2: exhaustive decode (all 256 byte values) ───────────────────────


class TestE5M2Decode:
    """Verify decode_ofp8_e5m2 matches ml_dtypes for all 256 patterns."""

    @pytest.mark.parametrize("byte_val", range(256))
    def test_decode_all(self, byte_val: int) -> None:
        ours = decode_ofp8_e5m2(byte_val)
        ref = _ml_decode_e5m2(byte_val)
        assert _same_float(ours, ref), (
            f"E5M2 decode mismatch for 0x{byte_val:02X}: "
            f"ours={ours!r}, ml_dtypes={ref!r}"
        )


# ── E4M3: exhaustive encode (all representable values) ──────────────────


def _all_e4m3_representable() -> list[float]:
    """Return all distinct finite representable E4M3 values (+ and -)."""
    values: set[float] = set()
    for byte_val in range(256):
        v = _ml_decode_e4m3(byte_val)
        if math.isfinite(v):
            values.add(v)
    return sorted(values)


class TestE4M3Encode:
    """Verify encode_ofp8_e4m3 matches ml_dtypes for representable values."""

    @pytest.mark.parametrize(
        "value", _all_e4m3_representable(),
        ids=lambda v: f"{v:g}",
    )
    def test_encode_representable_rne(self, value: float) -> None:
        """Exact representable values must encode identically (RNE)."""
        ours_bytes, _ = encode_ofp8_e4m3(value, RoundingMode.RNE)
        ours = ours_bytes[0]
        ref = _ml_encode_e4m3(value)
        assert ours == ref, (
            f"E4M3 encode mismatch for {value!r}: "
            f"ours=0x{ours:02X}, ml_dtypes=0x{ref:02X}"
        )


# ── E5M2: exhaustive encode (all representable values) ──────────────────


def _all_e5m2_representable() -> list[float]:
    """Return all distinct finite representable E5M2 values (+ and -)."""
    values: set[float] = set()
    for byte_val in range(256):
        v = _ml_decode_e5m2(byte_val)
        if math.isfinite(v):
            values.add(v)
    return sorted(values)


class TestE5M2Encode:
    """Verify encode_ofp8_e5m2 matches ml_dtypes for representable values."""

    @pytest.mark.parametrize(
        "value", _all_e5m2_representable(),
        ids=lambda v: f"{v:g}",
    )
    def test_encode_representable_rne(self, value: float) -> None:
        """Exact representable values must encode identically (RNE)."""
        ours_bytes, _ = encode_ofp8_e5m2(value, RoundingMode.RNE)
        ours = ours_bytes[0]
        ref = _ml_encode_e5m2(value)
        assert ours == ref, (
            f"E5M2 encode mismatch for {value!r}: "
            f"ours=0x{ours:02X}, ml_dtypes=0x{ref:02X}"
        )


# ── E4M3: midpoint rounding (RNE) ──────────────────────────────────────


def _e4m3_midpoints() -> list[tuple[float, int]]:
    """Generate midpoints between consecutive E4M3 values with expected RNE.

    For each pair of adjacent representable values (a, b), the midpoint
    (a+b)/2 should round to the value with an even trailing bit under RNE.
    We use ml_dtypes as the oracle for expected encoding.
    """
    reps = _all_e4m3_representable()
    positive = sorted(v for v in reps if v > 0)
    pairs: list[tuple[float, int]] = []
    for i in range(len(positive) - 1):
        mid = (positive[i] + positive[i + 1]) / 2.0
        ref = _ml_encode_e4m3(mid)
        pairs.append((mid, ref))
    return pairs


class TestE4M3Rounding:
    """Test RNE rounding at midpoints between representable E4M3 values."""

    @pytest.mark.parametrize(
        "mid,expected_byte", _e4m3_midpoints(),
        ids=lambda x: f"{x:g}" if isinstance(x, float) else f"0x{x:02X}",
    )
    def test_midpoint_rne(self, mid: float, expected_byte: int) -> None:
        ours_bytes, _ = encode_ofp8_e4m3(mid, RoundingMode.RNE)
        assert ours_bytes[0] == expected_byte, (
            f"E4M3 RNE midpoint mismatch for {mid!r}: "
            f"ours=0x{ours_bytes[0]:02X}, expected=0x{expected_byte:02X}"
        )


# ── E5M2: midpoint rounding (RNE) ──────────────────────────────────────


def _e5m2_midpoints() -> list[tuple[float, int]]:
    """Generate midpoints between consecutive E5M2 values with expected RNE."""
    reps = _all_e5m2_representable()
    positive = sorted(v for v in reps if v > 0)
    pairs: list[tuple[float, int]] = []
    for i in range(len(positive) - 1):
        mid = (positive[i] + positive[i + 1]) / 2.0
        ref = _ml_encode_e5m2(mid)
        pairs.append((mid, ref))
    return pairs


class TestE5M2Rounding:
    """Test RNE rounding at midpoints between representable E5M2 values."""

    @pytest.mark.parametrize(
        "mid,expected_byte", _e5m2_midpoints(),
        ids=lambda x: f"{x:g}" if isinstance(x, float) else f"0x{x:02X}",
    )
    def test_midpoint_rne(self, mid: float, expected_byte: int) -> None:
        ours_bytes, _ = encode_ofp8_e5m2(mid, RoundingMode.RNE)
        assert ours_bytes[0] == expected_byte, (
            f"E5M2 RNE midpoint mismatch for {mid!r}: "
            f"ours=0x{ours_bytes[0]:02X}, expected=0x{expected_byte:02X}"
        )


# ── Special values ──────────────────────────────────────────────────────


class TestE4M3Specials:
    """E4M3 special value handling."""

    def test_nan_encodes_to_0x7f(self) -> None:
        data, exc = encode_ofp8_e4m3(float("nan"))
        assert data == b"\x7f"
        assert exc.invalid is True

    def test_neg_nan_encodes_to_0x7f(self) -> None:
        """E4M3 canonical NaN is always 0x7F (positive)."""
        data, _ = encode_ofp8_e4m3(float("-nan"))
        assert data == b"\x7f"

    def test_inf_saturates(self) -> None:
        """E4M3 has no infinity; +Inf saturates to max finite (0x7E=448)."""
        data, exc = encode_ofp8_e4m3(float("inf"))
        assert data[0] == 0x7E
        assert exc.overflow is True
        assert decode_ofp8_e4m3(0x7E) == 448.0

    def test_neg_inf_saturates(self) -> None:
        data, exc = encode_ofp8_e4m3(float("-inf"))
        assert data[0] == 0xFE
        assert exc.overflow is True
        assert decode_ofp8_e4m3(0xFE) == -448.0

    def test_positive_zero(self) -> None:
        data, exc = encode_ofp8_e4m3(0.0)
        assert data == b"\x00"
        assert exc == (False, False, False, False, False)

    def test_negative_zero(self) -> None:
        data, exc = encode_ofp8_e4m3(-0.0)
        assert data == b"\x80"
        assert exc == (False, False, False, False, False)

    def test_max_finite(self) -> None:
        data, _ = encode_ofp8_e4m3(448.0)
        assert data[0] == 0x7E
        ref = _ml_encode_e4m3(448.0)
        assert data[0] == ref

    def test_overflow_above_max(self) -> None:
        """Value > 448 saturates to max (E4M3 has no Inf)."""
        data, exc = encode_ofp8_e4m3(500.0)
        assert data[0] == 0x7E
        assert exc.overflow is True

    def test_smallest_subnormal(self) -> None:
        """Smallest positive E4M3 subnormal: 2^(-6-3) * 1 = 2^-9."""
        smallest = 2**-9  # 0.001953125
        data, _ = encode_ofp8_e4m3(smallest)
        ref = _ml_encode_e4m3(smallest)
        assert data[0] == ref
        assert decode_ofp8_e4m3(data[0]) == smallest


class TestE5M2Specials:
    """E5M2 special value handling."""

    def test_nan_encodes(self) -> None:
        data, exc = encode_ofp8_e5m2(float("nan"))
        # Our canonical NaN is 0x7D (exp=31, mant=01)
        assert data == b"\x7d"
        assert exc.invalid is True

    def test_positive_inf(self) -> None:
        data, exc = encode_ofp8_e5m2(float("inf"))
        assert data[0] == 0x7C  # exp=31, mant=00
        assert exc == (False, False, False, False, False)
        assert math.isinf(decode_ofp8_e5m2(0x7C))

    def test_negative_inf(self) -> None:
        data, exc = encode_ofp8_e5m2(float("-inf"))
        assert data[0] == 0xFC
        assert math.isinf(decode_ofp8_e5m2(0xFC))
        assert decode_ofp8_e5m2(0xFC) < 0

    def test_positive_zero(self) -> None:
        data, _ = encode_ofp8_e5m2(0.0)
        assert data == b"\x00"

    def test_negative_zero(self) -> None:
        data, _ = encode_ofp8_e5m2(-0.0)
        assert data == b"\x80"

    def test_max_finite(self) -> None:
        data, _ = encode_ofp8_e5m2(57344.0)
        ref = _ml_encode_e5m2(57344.0)
        assert data[0] == ref

    def test_overflow_to_inf(self) -> None:
        """Value above RNE threshold (61440) overflows to Inf."""
        data, exc = encode_ofp8_e5m2(65536.0)
        assert decode_ofp8_e5m2(data[0]) == float("inf")
        assert exc.overflow is True

    def test_smallest_subnormal(self) -> None:
        """Smallest positive E5M2 subnormal: 2^(-14-2) * 1 = 2^-16."""
        smallest = 2**-16
        data, _ = encode_ofp8_e5m2(smallest)
        ref = _ml_encode_e5m2(smallest)
        assert data[0] == ref
        assert decode_ofp8_e5m2(data[0]) == smallest


# ── Roundtrip: encode then decode ───────────────────────────────────────


class TestE4M3Roundtrip:
    """encode → decode roundtrip must be identity for representable values."""

    @pytest.mark.parametrize(
        "value", _all_e4m3_representable(),
        ids=lambda v: f"{v:g}",
    )
    def test_roundtrip(self, value: float) -> None:
        data, _ = encode_ofp8_e4m3(value, RoundingMode.RNE)
        decoded = decode_ofp8_e4m3(data[0])
        assert _same_float_strict(decoded, value), (
            f"E4M3 roundtrip fail: {value!r} → 0x{data[0]:02X} → {decoded!r}"
        )


class TestE5M2Roundtrip:
    """encode → decode roundtrip must be identity for representable values."""

    @pytest.mark.parametrize(
        "value", _all_e5m2_representable(),
        ids=lambda v: f"{v:g}",
    )
    def test_roundtrip(self, value: float) -> None:
        data, _ = encode_ofp8_e5m2(value, RoundingMode.RNE)
        decoded = decode_ofp8_e5m2(data[0])
        assert _same_float_strict(decoded, value), (
            f"E5M2 roundtrip fail: {value!r} → 0x{data[0]:02X} → {decoded!r}"
        )


# ── Cross-format encode: random f32 values through both libraries ───────


def _sample_f32_values() -> list[float]:
    """Generate a spread of float32 values to test encoding."""
    values: list[float] = []
    # Powers of 2
    for e in range(-20, 20):
        values.append(2.0**e)
        values.append(-(2.0**e))
    # Small integers
    for i in range(1, 50):
        values.append(float(i))
        values.append(float(-i))
    # Fractions
    for denom in (3, 7, 10, 13, 100):
        for num in range(1, 10):
            values.append(num / denom)
            values.append(-num / denom)
    # Near boundaries
    values.extend([448.0, 449.0, 447.0, 0.5, 0.25, 0.125])
    values.extend([57344.0, 57345.0, 57343.0])
    # Very small
    values.extend([1e-10, 1e-5, 1e-3])
    return values


class TestE4M3CrossEncode:
    """Encode arbitrary f32 values and compare byte output with ml_dtypes.

    Known divergence (OFP8 §5.2.1 Table 3):
      ml_dtypes float8_e4m3fn uses NONSAT mode (overflow → NaN=0x7F).
      Our encoder uses SAT mode (overflow → max_finite=0x7E).
      Both are valid per OFP8; we skip overflow cases.
    """

    @pytest.mark.parametrize(
        "value", _sample_f32_values(),
        ids=lambda v: f"{v:g}",
    )
    def test_encode_matches(self, value: float) -> None:
        ours_bytes, _ = encode_ofp8_e4m3(value, RoundingMode.RNE)
        ref = _ml_encode_e4m3(value)
        ref_val = _ml_decode_e4m3(ref)
        if math.isnan(ref_val) and not math.isnan(value):
            # OFP8 §5.2.1 Table 3: NONSAT→NaN vs our SAT→max_finite
            pytest.skip("E4M3 SAT/NONSAT divergence (OFP8 Table 3)")
        assert ours_bytes[0] == ref, (
            f"E4M3 encode mismatch for {value!r}: "
            f"ours=0x{ours_bytes[0]:02X}, ml_dtypes=0x{ref:02X} "
            f"(ours_dec={decode_ofp8_e4m3(ours_bytes[0])!r}, "
            f"ref_dec={ref_val!r})"
        )


class TestE5M2CrossEncode:
    """Encode arbitrary f32 values and compare byte output with ml_dtypes.

    E5M2 follows IEEE 754 (NONSAT mode per OFP8 §5.2.1 Table 3):
    overflow → ±Inf, matching ml_dtypes float8_e5m2 behavior.
    """

    @pytest.mark.parametrize(
        "value", _sample_f32_values(),
        ids=lambda v: f"{v:g}",
    )
    def test_encode_matches(self, value: float) -> None:
        ref = _ml_encode_e5m2(value)
        ours_bytes, _ = encode_ofp8_e5m2(value, RoundingMode.RNE)
        assert ours_bytes[0] == ref, (
            f"E5M2 encode mismatch for {value!r}: "
            f"ours=0x{ours_bytes[0]:02X}, ml_dtypes=0x{ref:02X} "
            f"(ours_dec={decode_ofp8_e5m2(ours_bytes[0])!r}, "
            f"ref_dec={_ml_decode_e5m2(ref)!r})"
        )


# ── Exception flags sanity ──────────────────────────────────────────────


class TestExceptionFlags:
    """Verify exception flags are set correctly for known cases."""

    def test_e4m3_exact_no_flags(self) -> None:
        """Encoding an exact representable value raises no flags."""
        _, exc = encode_ofp8_e4m3(1.0)
        assert exc == (False, False, False, False, False)

    def test_e4m3_inexact_on_rounding(self) -> None:
        """Encoding a value that requires rounding sets inexact."""
        _, exc = encode_ofp8_e4m3(1.1)
        assert exc.inexact is True

    def test_e4m3_overflow_flags(self) -> None:
        _, exc = encode_ofp8_e4m3(500.0)
        assert exc.overflow is True
        assert exc.inexact is True

    def test_e4m3_underflow_on_subnormal(self) -> None:
        """Encoding a value in the subnormal range sets underflow."""
        _, exc = encode_ofp8_e4m3(2**-9)  # smallest subnormal, exact
        # Exact subnormal: underflow is set (tininess before rounding)
        assert exc.underflow is True

    def test_e5m2_exact_no_flags(self) -> None:
        _, exc = encode_ofp8_e5m2(1.0)
        assert exc == (False, False, False, False, False)

    def test_e5m2_inexact_on_rounding(self) -> None:
        _, exc = encode_ofp8_e5m2(1.1)
        assert exc.inexact is True

    def test_e5m2_overflow_flags(self) -> None:
        _, exc = encode_ofp8_e5m2(100000.0)
        assert exc.overflow is True
        assert exc.inexact is True

    def test_e5m2_underflow_on_subnormal(self) -> None:
        _, exc = encode_ofp8_e5m2(2**-16)
        assert exc.underflow is True


# ════════════════════════════════════════════════════════════════════════
# OFP8 §5.2.1 Table 3 — conversion behavior tests
# ════════════════════════════════════════════════════════════════════════
#
# Verify that our implementation matches the OFP8 conversion semantics:
#   E4M3: SAT mode — overflow saturates to ±max_finite (448)
#   E5M2: IEEE 754 / NONSAT — overflow produces ±Inf


class TestOFP8Table3E4M3:
    """OFP8 §5.2.1 Table 3 — E4M3 SAT conversion mode."""

    # E4M3 max finite = 448, ULP at max binade = 32
    # RNE threshold = 448 + 16 = 464

    def test_overflow_positive_saturates(self) -> None:
        """Positive overflow → +max_finite (0x7E = 448)."""
        data, exc = encode_ofp8_e4m3(500.0)
        assert data[0] == 0x7E
        assert decode_ofp8_e4m3(0x7E) == 448.0
        assert exc.overflow is True

    def test_overflow_negative_saturates(self) -> None:
        """Negative overflow → -max_finite (0xFE = -448)."""
        data, exc = encode_ofp8_e4m3(-500.0)
        assert data[0] == 0xFE
        assert decode_ofp8_e4m3(0xFE) == -448.0
        assert exc.overflow is True

    def test_inf_saturates(self) -> None:
        """No Inf in E4M3: +Inf → +max_finite."""
        data, exc = encode_ofp8_e4m3(float("inf"))
        assert data[0] == 0x7E
        assert exc.overflow is True

    def test_neg_inf_saturates(self) -> None:
        """No Inf in E4M3: -Inf → -max_finite."""
        data, exc = encode_ofp8_e4m3(float("-inf"))
        assert data[0] == 0xFE
        assert exc.overflow is True

    def test_nan_preserved(self) -> None:
        """NaN input → NaN (0x7F), regardless of SAT/NONSAT."""
        data, exc = encode_ofp8_e4m3(float("nan"))
        assert data[0] == 0x7F
        assert math.isnan(decode_ofp8_e4m3(0x7F))
        assert exc.invalid is True

    def test_near_overflow_rounds_to_max(self) -> None:
        """Value just above max (449) rounds to max under RNE."""
        data, _ = encode_ofp8_e4m3(449.0, RoundingMode.RNE)
        assert data[0] == 0x7E  # 448

    def test_at_rne_threshold_rounds_to_max(self) -> None:
        """At RNE threshold (464 = 448 + ULP/2), tie→even = max."""
        data, _ = encode_ofp8_e4m3(464.0, RoundingMode.RNE)
        assert data[0] == 0x7E  # 448 (even mantissa)

    def test_above_rne_threshold_still_saturates(self) -> None:
        """Above RNE threshold (465), would overflow but SAT → max."""
        data, exc = encode_ofp8_e4m3(465.0, RoundingMode.RNE)
        assert data[0] == 0x7E  # 448, not NaN
        assert exc.overflow is True

    def test_underflow_to_subnormal(self) -> None:
        """Tiny value encodes as subnormal, sets underflow flag."""
        data, exc = encode_ofp8_e4m3(2**-9)  # smallest subnormal
        assert data[0] == 0x01
        assert exc.underflow is True


class TestOFP8Table3E5M2:
    """OFP8 §5.2.1 Table 3 — E5M2 IEEE 754 (NONSAT) conversion mode."""

    # E5M2 max finite = 57344, ULP at max binade = 8192
    # RNE threshold = 57344 + 4096 = 61440

    def test_overflow_positive_to_inf(self) -> None:
        """Positive overflow → +Inf (0x7C)."""
        data, exc = encode_ofp8_e5m2(100000.0)
        assert data[0] == 0x7C
        assert math.isinf(decode_ofp8_e5m2(0x7C))
        assert exc.overflow is True

    def test_overflow_negative_to_inf(self) -> None:
        """Negative overflow → -Inf (0xFC)."""
        data, exc = encode_ofp8_e5m2(-100000.0)
        assert data[0] == 0xFC
        assert math.isinf(decode_ofp8_e5m2(0xFC))
        assert exc.overflow is True

    def test_near_max_rounds_to_max(self) -> None:
        """57345 is above MAX but below RNE threshold → rounds to MAX."""
        data, _ = encode_ofp8_e5m2(57345.0, RoundingMode.RNE)
        assert data[0] == 0x7B  # MAX = 57344

    def test_below_rne_threshold_rounds_to_max(self) -> None:
        """61439 < RNE threshold (61440) → rounds to MAX."""
        data, _ = encode_ofp8_e5m2(61439.0, RoundingMode.RNE)
        assert data[0] == 0x7B  # MAX = 57344

    def test_at_rne_threshold_overflows(self) -> None:
        """At RNE threshold (61440 = MAX + ULP/2), tie→even = Inf."""
        data, exc = encode_ofp8_e5m2(61440.0, RoundingMode.RNE)
        assert data[0] == 0x7C  # +Inf
        assert exc.overflow is True

    def test_above_rne_threshold_overflows(self) -> None:
        """Above RNE threshold → Inf."""
        data, exc = encode_ofp8_e5m2(65536.0, RoundingMode.RNE)
        assert data[0] == 0x7C
        assert exc.overflow is True

    def test_rtz_near_max_stays_max(self) -> None:
        """RTZ: 60000 > MAX but truncates to MAX (toward zero)."""
        data, _ = encode_ofp8_e5m2(60000.0, RoundingMode.RTZ)
        assert data[0] == 0x7B  # MAX

    def test_rup_positive_near_max_overflows(self) -> None:
        """RUP: positive 57345 > MAX → Inf (round toward +Inf)."""
        data, exc = encode_ofp8_e5m2(57345.0, RoundingMode.RUP)
        assert data[0] == 0x7C  # +Inf
        assert exc.overflow is True

    def test_rdn_negative_near_max_overflows(self) -> None:
        """RDN: negative -57345 → -Inf (round toward -Inf)."""
        data, exc = encode_ofp8_e5m2(-57345.0, RoundingMode.RDN)
        assert data[0] == 0xFC  # -Inf
        assert exc.overflow is True

    def test_rdn_positive_near_max_stays_max(self) -> None:
        """RDN: positive 60000 > MAX truncates to MAX (toward -Inf)."""
        data, _ = encode_ofp8_e5m2(60000.0, RoundingMode.RDN)
        assert data[0] == 0x7B  # MAX

    def test_nan_preserved(self) -> None:
        """NaN input → NaN."""
        data, exc = encode_ofp8_e5m2(float("nan"))
        assert math.isnan(decode_ofp8_e5m2(data[0]))
        assert exc.invalid is True

    def test_underflow_to_subnormal(self) -> None:
        """Tiny value encodes as subnormal, sets underflow flag."""
        data, exc = encode_ofp8_e5m2(2**-16)  # smallest subnormal
        assert data[0] == 0x01
        assert exc.underflow is True


# ════════════════════════════════════════════════════════════════════════
# Arithmetic cross-validation against ml_dtypes
# ════════════════════════════════════════════════════════════════════════
#
# Note: OFP8 §4 explicitly states arithmetic on OFP8 formats is out of
# scope.  Both our code and ml_dtypes compute in float64, then re-encode
# to fp8.  The only divergence is E4M3 overflow handling (SAT vs NONSAT
# per OFP8 §5.2.1 Table 3).

_FMT_O3 = 3  # E4M3 format code
_FMT_O2 = 4  # E5M2 format code

# Representative E4M3 byte values: zeros, NaN, subnormals,
# small / medium / large normals, max, negatives.
_E4M3_ARITH: list[int] = [
    0x00,  # +0.0
    0x80,  # -0.0
    0x7F,  # NaN
    0x01,  # min subnormal  (2^-9)
    0x04,  # subnormal
    0x07,  # max subnormal  (7·2^-9)
    0x08,  # min normal     (2^-6)
    0x20,  # 0.125
    0x30,  # 0.5
    0x38,  # 1.0
    0x3C,  # 1.5
    0x40,  # 2.0
    0x48,  # 4.0
    0x60,  # 32.0
    0x70,  # 128.0
    0x7E,  # 448.0 (max)
    0xB8,  # -1.0
    0xC0,  # -2.0
    0xFE,  # -448.0
]

# Representative E5M2 byte values (includes ±Inf).
_E5M2_ARITH: list[int] = [
    0x00,  # +0.0
    0x80,  # -0.0
    0x7C,  # +Inf
    0xFC,  # -Inf
    0x7D,  # NaN
    0x01,  # min subnormal  (2^-16)
    0x03,  # max subnormal  (3·2^-16)
    0x04,  # min normal     (2^-14)
    0x10,  # 2^-11
    0x20,  # 2^-7
    0x30,  # 0.125
    0x3C,  # 1.0
    0x3E,  # 1.5
    0x40,  # 2.0
    0x50,  # 32.0
    0x60,  # 512.0
    0x70,  # 8192.0
    0x7B,  # 57344.0 (max)
    0xBC,  # -1.0
    0xFB,  # -57344.0
]

_FP_OPS = {"+": fp_add, "-": fp_sub, "*": fp_mul, "/": fp_div}


def _pairs(byte_list: list[int]) -> list[tuple[int, int]]:
    return [(a, b) for a in byte_list for b in byte_list]


def _pair_ids(byte_list: list[int]) -> list[str]:
    return [f"0x{a:02X}_0x{b:02X}" for a, b in _pairs(byte_list)]


def _byte_ids(byte_list: list[int]) -> list[str]:
    return [f"0x{v:02X}" for v in byte_list]


# ── ml_dtypes computation helpers ───────────────────────────────────


def _ml_binary(
    op: str, a_byte: int, b_byte: int, ml_dtype: type,
) -> int:
    """Compute a binary op via ml_dtypes, return result byte."""
    a = np.float64(np.frombuffer(bytes([a_byte]), dtype=ml_dtype)[0])
    b = np.float64(np.frombuffer(bytes([b_byte]), dtype=ml_dtype)[0])
    with np.errstate(all="ignore"):
        if op == "+":
            r = a + b
        elif op == "-":
            r = a - b
        elif op == "*":
            r = a * b
        else:
            r = a / b
        return int(np.array([float(r)]).astype(ml_dtype).view(np.uint8)[0])


def _ml_sqrt_byte(v_byte: int, ml_dtype: type) -> int:
    """Compute sqrt via ml_dtypes, return result byte."""
    v = np.float64(np.frombuffer(bytes([v_byte]), dtype=ml_dtype)[0])
    with np.errstate(all="ignore"):
        r = np.sqrt(v)
        return int(np.array([float(r)]).astype(ml_dtype).view(np.uint8)[0])


# ── our computation helpers ─────────────────────────────────────────


def _our_binary(
    op: str, a_byte: int, b_byte: int,
    fmt: int, decode_fn: object, encode_fn: object,
) -> int:
    """Compute a binary op via our fp_formats, return result byte."""
    a_val = decode_fn(a_byte)
    b_val = decode_fn(b_byte)
    result, _ = _FP_OPS[op](a_val, b_val, fmt, RoundingMode.RNE)
    return encode_fn(result, RoundingMode.RNE)[0][0]


def _our_sqrt_byte(
    v_byte: int, fmt: int, decode_fn: object, encode_fn: object,
) -> int:
    """Compute sqrt via our fp_formats, return result byte."""
    v_val = decode_fn(v_byte)
    result, _ = fp_sqrt(v_val, fmt, RoundingMode.RNE)
    return encode_fn(result, RoundingMode.RNE)[0][0]


# ── comparison with known-divergence handling ───────────────────────


def _both_nan(byte_a: int, byte_b: int, decode_fn: object) -> bool:
    """True if both byte patterns decode to NaN (regardless of payload)."""
    return math.isnan(decode_fn(byte_a)) and math.isnan(decode_fn(byte_b))


def _check_binary(
    op: str, a_byte: int, b_byte: int,
    fmt: int, decode_fn: object, encode_fn: object,
    ml_dtype: type, *, has_inf: bool,
) -> None:
    ours = _our_binary(op, a_byte, b_byte, fmt, decode_fn, encode_fn)
    ref = _ml_binary(op, a_byte, b_byte, ml_dtype)
    if ours == ref:
        return

    # Different NaN bit patterns are both valid NaN representations.
    if _both_nan(ours, ref, decode_fn):
        return

    ours_val = decode_fn(ours)
    ref_val = float(np.frombuffer(bytes([ref]), dtype=ml_dtype)[0])

    # OFP8 §5.2.1 Table 3: E4M3 SAT→max vs NONSAT→NaN
    if not has_inf and math.isnan(ref_val) and not math.isnan(ours_val):
        pytest.skip("E4M3 SAT/NONSAT divergence (OFP8 Table 3)")

    a_val = decode_fn(a_byte)
    b_val = decode_fn(b_byte)
    pytest.fail(
        f"{a_val!r} {op} {b_val!r} (0x{a_byte:02X} {op} 0x{b_byte:02X}): "
        f"ours=0x{ours:02X}({ours_val!r}), ref=0x{ref:02X}({ref_val!r})"
    )


def _check_sqrt(
    v_byte: int,
    fmt: int, decode_fn: object, encode_fn: object,
    ml_dtype: type, *, has_inf: bool,
) -> None:
    ours = _our_sqrt_byte(v_byte, fmt, decode_fn, encode_fn)
    ref = _ml_sqrt_byte(v_byte, ml_dtype)
    if ours == ref:
        return

    if _both_nan(ours, ref, decode_fn):
        return

    ours_val = decode_fn(ours)
    ref_val = float(np.frombuffer(bytes([ref]), dtype=ml_dtype)[0])

    # OFP8 §5.2.1 Table 3: E4M3 SAT→max vs NONSAT→NaN
    if not has_inf and math.isnan(ref_val) and not math.isnan(ours_val):
        pytest.skip("E4M3 SAT/NONSAT divergence (OFP8 Table 3)")

    v_val = decode_fn(v_byte)
    pytest.fail(
        f"sqrt({v_val!r}) (0x{v_byte:02X}): "
        f"ours=0x{ours:02X}({ours_val!r}), ref=0x{ref:02X}({ref_val!r})"
    )


# ── precomputed pairs ──────────────────────────────────────────────

_e4m3_pairs = _pairs(_E4M3_ARITH)
_e4m3_pids = _pair_ids(_E4M3_ARITH)
_e5m2_pairs = _pairs(_E5M2_ARITH)
_e5m2_pids = _pair_ids(_E5M2_ARITH)


# ── E4M3 arithmetic ────────────────────────────────────────────────


class TestE4M3Arith:
    """Cross-validate E4M3 add/sub/mul/div/sqrt against ml_dtypes."""

    @pytest.mark.parametrize("a,b", _e4m3_pairs, ids=_e4m3_pids)
    def test_add(self, a: int, b: int) -> None:
        _check_binary(
            "+", a, b, _FMT_O3,
            decode_ofp8_e4m3, encode_ofp8_e4m3, E4M3, has_inf=False,
        )

    @pytest.mark.parametrize("a,b", _e4m3_pairs, ids=_e4m3_pids)
    def test_sub(self, a: int, b: int) -> None:
        _check_binary(
            "-", a, b, _FMT_O3,
            decode_ofp8_e4m3, encode_ofp8_e4m3, E4M3, has_inf=False,
        )

    @pytest.mark.parametrize("a,b", _e4m3_pairs, ids=_e4m3_pids)
    def test_mul(self, a: int, b: int) -> None:
        _check_binary(
            "*", a, b, _FMT_O3,
            decode_ofp8_e4m3, encode_ofp8_e4m3, E4M3, has_inf=False,
        )

    @pytest.mark.parametrize("a,b", _e4m3_pairs, ids=_e4m3_pids)
    def test_div(self, a: int, b: int) -> None:
        _check_binary(
            "/", a, b, _FMT_O3,
            decode_ofp8_e4m3, encode_ofp8_e4m3, E4M3, has_inf=False,
        )

    @pytest.mark.parametrize("v", _E4M3_ARITH, ids=_byte_ids(_E4M3_ARITH))
    def test_sqrt(self, v: int) -> None:
        _check_sqrt(
            v, _FMT_O3,
            decode_ofp8_e4m3, encode_ofp8_e4m3, E4M3, has_inf=False,
        )


# ── E5M2 arithmetic ────────────────────────────────────────────────


class TestE5M2Arith:
    """Cross-validate E5M2 add/sub/mul/div/sqrt against ml_dtypes."""

    @pytest.mark.parametrize("a,b", _e5m2_pairs, ids=_e5m2_pids)
    def test_add(self, a: int, b: int) -> None:
        _check_binary(
            "+", a, b, _FMT_O2,
            decode_ofp8_e5m2, encode_ofp8_e5m2, E5M2, has_inf=True,
        )

    @pytest.mark.parametrize("a,b", _e5m2_pairs, ids=_e5m2_pids)
    def test_sub(self, a: int, b: int) -> None:
        _check_binary(
            "-", a, b, _FMT_O2,
            decode_ofp8_e5m2, encode_ofp8_e5m2, E5M2, has_inf=True,
        )

    @pytest.mark.parametrize("a,b", _e5m2_pairs, ids=_e5m2_pids)
    def test_mul(self, a: int, b: int) -> None:
        _check_binary(
            "*", a, b, _FMT_O2,
            decode_ofp8_e5m2, encode_ofp8_e5m2, E5M2, has_inf=True,
        )

    @pytest.mark.parametrize("a,b", _e5m2_pairs, ids=_e5m2_pids)
    def test_div(self, a: int, b: int) -> None:
        _check_binary(
            "/", a, b, _FMT_O2,
            decode_ofp8_e5m2, encode_ofp8_e5m2, E5M2, has_inf=True,
        )

    @pytest.mark.parametrize("v", _E5M2_ARITH, ids=_byte_ids(_E5M2_ARITH))
    def test_sqrt(self, v: int) -> None:
        _check_sqrt(
            v, _FMT_O2,
            decode_ofp8_e5m2, encode_ofp8_e5m2, E5M2, has_inf=True,
        )
