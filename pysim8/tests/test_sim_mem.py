"""Memory model tests from spec/tests/tests-mem.md (M10-M23)."""

from __future__ import annotations

import pytest
from conftest import run

from pysim8.asm import assemble
from pysim8.sim import CPU, CpuState
from pysim8.sim.errors import ErrorCode


def _run_fp(source: str) -> tuple[CPU, dict[str, int]]:
    """Assemble at arch=2, run, return (cpu, labels)."""
    result = assemble(source, arch=2)
    cpu = CPU(arch=2)
    cpu.load(result.code)
    cpu.run()
    return cpu, result.labels


def _run_vu(source: str) -> tuple[CPU, dict[str, int]]:
    """Assemble at arch=3, run, return (cpu, labels)."""
    result = assemble(source, arch=3)
    cpu = CPU(arch=3)
    cpu.load(result.code)
    cpu.run()
    return cpu, result.labels


# ── M.1 Memory Initialization ────────────────────────────────────


class TestMemInit:
    """Spec §M.1 — memory initialised to zero."""

    def test_m10_page0_noncode_zero(self) -> None:
        cpu = run("MOV A, [0x10]\nHLT")
        assert cpu.a == 0

    def test_m11_extended_page_zero(self) -> None:
        cpu = run("MOV DP, 5\nMOV A, [0]\nHLT")
        assert cpu.a == 0


# ── M.2 FP Byte Ordering ─────────────────────────────────────────


class TestFpByteOrdering:
    """Spec §M.2 — FP memory access is little-endian."""

    def test_m12_load_f32_le(self) -> None:
        # float32 1.0 = 0x3F800000 → bytes [0x00, 0x00, 0x80, 0x3F]
        src = "FMOV.F FA, [data]\nHLT\ndata: DB 0x00,0x00,0x80,0x3F"
        cpu, _ = _run_fp(src)
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.fa == 0x3F800000

    def test_m13_store_f32_le(self) -> None:
        src = "FMOV.F FA, [data]\nFMOV.F [out], FA\nHLT\ndata: DB 0x00,0x00,0x80,0x3F\nout: DB 0,0,0,0\n"
        cpu, labels = _run_fp(src)
        addr = labels["out"]
        assert [cpu.mem[addr + i] for i in range(4)] == [0x00, 0x00, 0x80, 0x3F]

    def test_m14_load_f16_le(self) -> None:
        # float16 1.0 = 0x3C00 → bytes [0x00, 0x3C]
        src = "FMOV.H FHA, [data]\nHLT\ndata: DB 0x00,0x3C"
        cpu, _ = _run_fp(src)
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.read_bits(0, 1) == 0x3C00

    def test_m15_load_bf16_le(self) -> None:
        # bfloat16 1.0 = 0x3F80 → bytes [0x80, 0x3F]
        src = "FMOV.BF FHA, [data]\nHLT\ndata: DB 0x80,0x3F"
        cpu, _ = _run_fp(src)
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.read_bits(0, 2) == 0x3F80


class TestFpPageBoundary:
    """Spec §M.2.1 — FP multi-byte access across page boundary faults."""

    def test_m16_f32_at_offset_254_faults(self) -> None:
        cpu, _ = _run_fp("MOV A, 254\nFMOV.F FA, [A]\nHLT")
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.PAGE_BOUNDARY)

    def test_m17_f16_at_offset_255_faults(self) -> None:
        cpu, _ = _run_fp("MOV A, 255\nFMOV.H FHA, [A]\nHLT")
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.PAGE_BOUNDARY)


# ── M.3 VU Memory Model ──────────────────────────────────────────


class TestVuMemoryModel:
    """Spec §M.3 — VU uses absolute 16-bit addresses; DP ignored."""

    def test_m18_vu_absolute_addressing_ignores_dp(self) -> None:
        src = (
            "MOV DP, 5\n"
            "VSET VA, 2, 0\n"  # VA = 0x0200
            "VSET VC, 2, 0\n"  # VC = 0x0200
            "VSET VL, 0, 4\n"  # VL = 4
            "VADD.U VC, VA, 1\n"
            "VWAIT\n"
            "HLT\n"
        )
        cpu, _ = _run_vu(src)
        # VU wrote to absolute 0x0200 (not DP-relative 5×256+0x200)
        assert cpu.mem[0x0200] == 1
        assert cpu.mem[0x0201] == 1
        assert cpu.mem[0x0202] == 1
        assert cpu.mem[0x0203] == 1

    def test_m19_vu_cross_page_access(self) -> None:
        src = (
            "VSET VA, 0, 0xFE\n"  # VA = 0xFE (page 0, near end)
            "VSET VC, 0, 0xFE\n"  # VC = 0xFE
            "VSET VL, 0, 4\n"  # VL = 4 elements
            "VADD.U VC, VA, 1\n"
            "VWAIT\n"
            "HLT\n"
        )
        cpu, _ = _run_vu(src)
        # 4 UINT8 elements cross page boundary (0xFE, 0xFF, 0x100, 0x101)
        assert cpu.mem[0xFE] == 1
        assert cpu.mem[0xFF] == 1
        assert cpu.mem[0x100] == 1
        assert cpu.mem[0x101] == 1

    def test_m20_vu_f16_byte_ordering(self) -> None:
        # Write float16(1.0) = [0x00, 0x3C] at address 0x100
        # VMOV.H copies it to 0x110 — verify LE byte order preserved
        src = (
            "MOV DP, 1\n"
            "MOV [0], 0x00\n"  # addr 0x100
            "MOV [1], 0x3C\n"  # addr 0x101
            "MOV DP, 0\n"
            "VSET VA, 1, 0\n"  # VA = 0x100
            "VSET VC, 1, 16\n"  # VC = 0x110
            "VSET VL, 0, 1\n"
            "VMOV.H VC, VA\n"
            "VWAIT\n"
            "HLT\n"
        )
        cpu, _ = _run_vu(src)
        assert cpu.mem[0x110] == 0x00
        assert cpu.mem[0x111] == 0x3C


# ── M.4 Stack Addressing ─────────────────────────────────────────


class TestStackAddressing:
    """Spec §M.4 — stack always on page 0 regardless of DP."""

    def test_m21_push_pop_with_nonzero_dp(self) -> None:
        cpu = run("MOV DP, 2\nMOV A, 42\nPUSH A\nPOP B\nHLT")
        assert cpu.b == 42

    def test_m22_sp_relative_read_after_push(self) -> None:
        cpu = run("MOV A, 42\nPUSH A\nMOV A, [SP+1]\nHLT")
        assert cpu.a == 42

    def test_m23_sp_indirect_ignores_dp(self) -> None:
        # Write to page 0 at SP_INIT offset (0xE7=231), then read back via [SP]
        # with DP=3 active — [SP] must use page 0, not DP page
        src = (
            "MOV DP, 0\n"
            "MOV [0xE7], 42\n"  # page 0 addr 231 = SP_INIT
            "MOV DP, 3\n"
            "MOV A, [SP]\n"  # must read page 0, not page 3
            "HLT\n"
        )
        cpu = run(src)
        assert cpu.a == 42
