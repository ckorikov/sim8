"""VCVT ↔ FCVT cross-validation tests.

Verifies that VCVT (element-wise format conversion in VU) produces
bit-identical results to FCVT (scalar FP register conversion) for each
supported format pair and representative input values.
"""

from __future__ import annotations

import pytest

from pysim8.asm import assemble
from pysim8.fp_formats import bytes_to_float, float_to_bytes
import struct

from pysim8.isa import (
    Op,
    VU_FMT_F,
    VU_FMT_H,
    VU_FMT_O3,
    VU_FMT_U,
    VU_MODE_R,
    encode_vfm,
    encode_vu_regs,
)
from pysim8.sim import CPU, CpuState
from pysim8.sim.errors import ErrorCode

_FMT_SIZE: dict[str, int] = {"F": 4, "H": 2, "O3": 1}


def _run_comparison(
    src_bytes: bytes,
    src_sfx: str,
    dst_sfx: str,
    fp_src: str,
    fp_dst: str,
) -> tuple[bytes, bytes]:
    """Run both FCVT and VCVT on the same src_bytes; return (fcvt_out, vcvt_out).

    Memory layout:
      0x40..: src_bytes (input value in src_sfx format)
      0x60..: FCVT output (dst_sfx bytes)
      0x70..: VCVT output (dst_sfx bytes)
    """
    dst_sz = _FMT_SIZE[dst_sfx]
    src = (
        f"FMOV.{src_sfx} {fp_src}, [0x40]\n"
        f"FCVT.{dst_sfx}.{src_sfx} {fp_dst}, {fp_src}\n"
        f"FMOV.{dst_sfx} [0x60], {fp_dst}\n"
        f"VSET VA, 0, 0x40\n"
        f"VSET VB, 0, 0x70\n"
        f"VSET VL, 0, 1\n"
        f"VCVT.{dst_sfx}.{src_sfx} VB, VA\n"
        f"VWAIT\n"
        f"HLT\n"
    )
    result = assemble(src, arch=3)
    cpu = CPU(arch=3)
    cpu.load(result.code)
    for i, b in enumerate(src_bytes):
        cpu.mem[0x40 + i] = b
    cpu.run()
    assert cpu.state == CpuState.HALTED, f"CPU faulted: state={cpu.state}, error_code={cpu.a}"
    fcvt_out = bytes(cpu.mem[0x60 + i] for i in range(dst_sz))
    vcvt_out = bytes(cpu.mem[0x70 + i] for i in range(dst_sz))
    return fcvt_out, vcvt_out


# ── Representative test values (little-endian raw bytes) ──────────

_F32_VALS = [
    (b"\x00\x00\x80\x3f", "1.0"),
    (b"\x00\x00\x80\xbf", "-1.0"),
    (b"\x00\x00\x00\x00", "0.0"),
    (b"\x00\x00\x80\x7f", "+inf"),
    (b"\x00\x00\xc0\x7f", "nan"),
    (b"\xab\xaa\xaa\x3e", "0.333"),
]

_F16_VALS = [
    (b"\x00\x3c", "1.0"),
    (b"\x00\xbc", "-1.0"),
    (b"\x00\x00", "0.0"),
    (b"\x00\x7c", "+inf"),
    (b"\x00\x7e", "nan"),
    (b"\x55\x35", "0.333"),
]

_O3_VALS = [
    (b"\x38", "1.0"),
    (b"\xb8", "-1.0"),
    (b"\x00", "0.0"),
    (b"\x30", "0.5"),
    (b"\x77", "max_finite"),
    (b"\x7f", "nan"),
]


# ── Cross-validation: VCVT output must match FCVT output bit-for-bit ─


class TestVcvtMatchesFcvt:
    """VCVT and FCVT must produce identical output bits for the same input."""

    @pytest.mark.parametrize("src_bytes,label", _F32_VALS, ids=[v[1] for v in _F32_VALS])
    def test_f32_to_f16(self, src_bytes: bytes, label: str) -> None:
        fcvt, vcvt = _run_comparison(src_bytes, "F", "H", "FA", "FHC")
        assert vcvt == fcvt, f"F32→F16 {label}: FCVT={fcvt.hex()} VCVT={vcvt.hex()}"

    @pytest.mark.parametrize("src_bytes,label", _F16_VALS, ids=[v[1] for v in _F16_VALS])
    def test_f16_to_f32(self, src_bytes: bytes, label: str) -> None:
        fcvt, vcvt = _run_comparison(src_bytes, "H", "F", "FHA", "FB")
        assert vcvt == fcvt, f"F16→F32 {label}: FCVT={fcvt.hex()} VCVT={vcvt.hex()}"

    @pytest.mark.parametrize("src_bytes,label", _F32_VALS, ids=[v[1] for v in _F32_VALS])
    def test_f32_to_o3(self, src_bytes: bytes, label: str) -> None:
        fcvt, vcvt = _run_comparison(src_bytes, "F", "O3", "FA", "FQE")
        assert vcvt == fcvt, f"F32→O3 {label}: FCVT={fcvt.hex()} VCVT={vcvt.hex()}"

    @pytest.mark.parametrize("src_bytes,label", _O3_VALS, ids=[v[1] for v in _O3_VALS])
    def test_o3_to_f32(self, src_bytes: bytes, label: str) -> None:
        fcvt, vcvt = _run_comparison(src_bytes, "O3", "F", "FQA", "FB")
        assert vcvt == fcvt, f"O3→F32 {label}: FCVT={fcvt.hex()} VCVT={vcvt.hex()}"

    @pytest.mark.parametrize("src_bytes,label", _F16_VALS, ids=[v[1] for v in _F16_VALS])
    def test_f16_to_o3(self, src_bytes: bytes, label: str) -> None:
        fcvt, vcvt = _run_comparison(src_bytes, "H", "O3", "FHA", "FQE")
        assert vcvt == fcvt, f"F16→O3 {label}: FCVT={fcvt.hex()} VCVT={vcvt.hex()}"

    @pytest.mark.parametrize("src_bytes,label", _O3_VALS, ids=[v[1] for v in _O3_VALS])
    def test_o3_to_f16(self, src_bytes: bytes, label: str) -> None:
        fcvt, vcvt = _run_comparison(src_bytes, "O3", "H", "FQA", "FHC")
        assert vcvt == fcvt, f"O3→F16 {label}: FCVT={fcvt.hex()} VCVT={vcvt.hex()}"


# ── VL > 1 ────────────────────────────────────────────────────────


class TestVcvtVl:
    """VCVT processes all VL elements sequentially."""

    def test_vcvt_vl4_f32_to_f16(self) -> None:
        """VCVT.H.F with VL=4 converts 4 float32 elements to float16."""
        # 1.0, 2.0, 3.0, 4.0 in F32 LE
        f32_vals = [0x3F800000, 0x40000000, 0x40400000, 0x40800000]
        src = "VSET VA, 0, 0x40\nVSET VB, 0, 0x60\nVSET VL, 0, 4\nVCVT.H.F VB, VA\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        for i, v in enumerate(f32_vals):
            for j in range(4):
                cpu.mem[0x40 + i * 4 + j] = (v >> (8 * j)) & 0xFF
        cpu.run()
        assert cpu.state == CpuState.HALTED
        for i, v in enumerate(f32_vals):
            raw32 = v.to_bytes(4, "little")
            f = bytes_to_float(raw32, VU_FMT_F)
            expected, _ = float_to_bytes(f, VU_FMT_H, 0)
            actual = bytes(cpu.mem[0x60 + i * 2 + j] for j in range(2))
            assert actual == expected, f"elem[{i}]: expected {expected.hex()}, got {actual.hex()}"

    def test_vcvt_vl3_o3_to_f32(self) -> None:
        """VCVT.F.O3 with VL=3 converts three O3 bytes to F32."""
        o3_vals = [0x38, 0xB8, 0x30]  # 1.0, -1.0, 0.5 in O3
        src = "VSET VA, 0, 0x40\nVSET VB, 0, 0x60\nVSET VL, 0, 3\nVCVT.F.O3 VB, VA\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        for i, v in enumerate(o3_vals):
            cpu.mem[0x40 + i] = v
        cpu.run()
        assert cpu.state == CpuState.HALTED
        for i, v in enumerate(o3_vals):
            f = bytes_to_float(bytes([v]), VU_FMT_O3)
            expected, _ = float_to_bytes(f, VU_FMT_F, 0)
            actual = bytes(cpu.mem[0x60 + i * 4 + j] for j in range(4))
            assert actual == expected, f"elem[{i}]: expected {expected.hex()}, got {actual.hex()}"


# ── Fault conditions ──────────────────────────────────────────────


class TestVcvtFaults:
    """VCVT fault conditions."""

    def test_vcvt_mode_r_faults(self) -> None:
        """VCVT with mode=R (manually encoded) → ERR_VU_FORMAT."""
        cpu = CPU(arch=3)
        code = (
            [int(Op.VSET_IMM16), 4, 1, 0]  # VSET VL, 1
            + [int(Op.VCVT), encode_vfm(VU_FMT_H, VU_MODE_R), encode_vfm(VU_FMT_F, 0), encode_vu_regs(1, 0, 0)]
            + [0]  # HLT
        )
        cpu.load(code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.VU_FORMAT)

    def test_vcvt_assembler_requires_two_suffixes(self) -> None:
        """Assembler raises AssemblerError when second format suffix is missing."""
        from pysim8.asm._codegen_core import AssemblerError

        with pytest.raises(AssemblerError, match="two format suffixes"):
            assemble("VSET VL, 0, 1\nVCVT.H VB, VA\nVWAIT\nHLT\n", arch=3)

    def test_vcvt_src_oob_faults_at_vwait(self) -> None:
        """VCVT src footprint beyond MEM_SIZE → deferred ERR_VU_OOB raised at VWAIT."""
        # VA=0xFFFC, VL=2, src_fmt=F32 (4 bytes/elem): footprint = 0xFFFC..0x10003 → OOB
        src = "VSET VA, 0xFF, 0xFC\nVSET VB, 0, 0x80\nVSET VL, 0, 2\nVCVT.H.F VB, VA\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.VU_OOB)


# ── Integer format conversions (FITOF/FFTOI analogues) ───────────────


class TestVcvtInteger:
    """VCVT with integer source or destination formats."""

    @pytest.mark.parametrize(
        "uint8_val,expected",
        [
            pytest.param(0, 0.0, id="zero"),
            pytest.param(1, 1.0, id="one"),
            pytest.param(128, 128.0, id="mid"),
            pytest.param(255, 255.0, id="max"),
        ],
    )
    def test_uint8_to_f32(self, uint8_val: int, expected: float) -> None:
        """VCVT.F.U: UINT8 → float32 (FITOF analogue)."""
        src = "VSET VA, 0, 0x40\nVSET VB, 0, 0x60\nVSET VL, 0, 1\nVCVT.F.U VB, VA\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        cpu.mem[0x40] = uint8_val
        cpu.run()
        assert cpu.state == CpuState.HALTED
        raw = bytes(cpu.mem[0x60 + j] for j in range(4))
        assert bytes_to_float(raw, VU_FMT_F) == expected

    @pytest.mark.parametrize(
        "uint8_val,expected",
        [
            pytest.param(0, 0.0, id="zero"),
            pytest.param(1, 1.0, id="one"),
            pytest.param(128, 128.0, id="mid"),
            pytest.param(255, 255.0, id="max"),
        ],
    )
    def test_uint8_to_f16(self, uint8_val: int, expected: float) -> None:
        """VCVT.H.U: UINT8 → float16."""
        src = "VSET VA, 0, 0x40\nVSET VB, 0, 0x60\nVSET VL, 0, 1\nVCVT.H.U VB, VA\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        cpu.mem[0x40] = uint8_val
        cpu.run()
        assert cpu.state == CpuState.HALTED
        raw = bytes(cpu.mem[0x60 + j] for j in range(2))
        assert bytes_to_float(raw, VU_FMT_H) == expected

    @pytest.mark.parametrize(
        "fp_val,expected_byte",
        [
            pytest.param(0.0, 0, id="zero"),
            pytest.param(1.0, 1, id="one"),
            pytest.param(128.0, 128, id="mid"),
            pytest.param(255.0, 255, id="max"),
            pytest.param(300.0, 255, id="clamp_high"),
            pytest.param(-5.0, 0, id="clamp_low"),
        ],
    )
    def test_f32_to_uint8_saturating(self, fp_val: float, expected_byte: int) -> None:
        """VCVT.U.F: float32 → UINT8 saturating (FFTOI analogue)."""
        src = "VSET VA, 0, 0x40\nVSET VB, 0, 0x60\nVSET VL, 0, 1\nVCVT.U.F VB, VA\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        for j, b in enumerate(struct.pack("<f", fp_val)):
            cpu.mem[0x40 + j] = b
        cpu.run()
        assert cpu.state == CpuState.HALTED
        assert cpu.mem[0x60] == expected_byte

    def test_vcvt_vl4_uint8_to_f32(self) -> None:
        """VCVT.F.U with VL=4 converts 4 UINT8 elements to float32."""
        vals = [0, 1, 128, 255]
        src = "VSET VA, 0, 0x40\nVSET VB, 0, 0x60\nVSET VL, 0, 4\nVCVT.F.U VB, VA\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        for i, v in enumerate(vals):
            cpu.mem[0x40 + i] = v
        cpu.run()
        assert cpu.state == CpuState.HALTED
        for i, v in enumerate(vals):
            raw = bytes(cpu.mem[0x60 + i * 4 + j] for j in range(4))
            assert bytes_to_float(raw, VU_FMT_F) == float(v)
