"""Hypothesis-driven fuzz testing: generate random programs and verify invariants.

These tests don't compare JS vs Python (that's done in web/tests/cross_validate.test.js).
Instead, they verify that the Python simulator maintains structural invariants for ANY
valid program, catching crashes, hangs, and state corruption.
"""

from __future__ import annotations

import random

import pytest
from conftest import run
from hypothesis import given, settings
from hypothesis import strategies as st

from pysim8.asm import assemble
from pysim8.sim import CPU, CpuState
from pysim8.sim.memory import SP_INIT

# ── Program generator ────────────────────────────────────────────────

# Safe instructions that don't cause control flow issues
SAFE_INT_INSTRS = [
    "MOV A, {imm}",
    "MOV B, {imm}",
    "MOV C, {imm}",
    "MOV D, {imm}",
    "MOV A, B",
    "MOV B, A",
    "MOV C, D",
    "MOV D, C",
    "MOV [{addr}], A",
    "MOV A, [{addr}]",
    "ADD A, {imm}",
    "ADD A, B",
    "SUB A, {imm}",
    "SUB A, B",
    "INC A",
    "INC B",
    "DEC A",
    "DEC C",
    "AND A, {imm}",
    "OR A, {imm}",
    "XOR A, B",
    "NOT A",
    "SHL A, {shift}",
    "SHR A, {shift}",
    "CMP A, B",
    "CMP A, {imm}",
    "MUL {imm}",
    "MUL B",
]

SAFE_FP_INSTRS = [
    "FITOF.F FA, A",
    "FITOF.H FHA, B",
    "FMOV.F FA, FB",
    "FABS.F FA",
    "FNEG.F FA",
    "FADD.F FA, FB",
    "FSUB.F FA, FB",
    "FMUL.F FA, FB",
    "FCMP.F FA, FB",
    "FFTOI.F A, FA",
    "FSTAT B",
    "FCFG C",
    "FCLR",
]


def _fill_template(template: str, rng: random.Random) -> str:
    """Fill template placeholders with random values."""
    return template.format(
        imm=rng.randint(0, 255),
        addr=rng.randint(80, 200),
        shift=rng.randint(0, 255),
    )


def build_program(instrs: list[str], seed: int = 42, arch: int = 1) -> str:
    """Build a valid program from instruction templates."""
    rng = random.Random(seed)
    lines = [
        f"MOV A, {rng.randint(0, 255)}",
        f"MOV B, {rng.randint(1, 255)}",  # B >= 1 to avoid DIV 0
        f"MOV C, {rng.randint(0, 255)}",
        f"MOV D, {rng.randint(0, 255)}",
    ]
    for tmpl in instrs:
        lines.append(_fill_template(tmpl, rng))
    lines.append("HLT")
    return "\n".join(lines)


# ── Strategies ───────────────────────────────────────────────────────

_int_instrs = st.lists(st.sampled_from(SAFE_INT_INSTRS), min_size=1, max_size=15)
_fp_instrs = st.lists(st.sampled_from(SAFE_INT_INSTRS + SAFE_FP_INSTRS), min_size=1, max_size=12)
_seed = st.integers(min_value=0, max_value=10000)


# ── Invariant tests ──────────────────────────────────────────────────


class TestIntegerInvariants:
    """Structural invariants for integer programs."""

    @given(instrs=_int_instrs, seed=_seed)
    @settings(max_examples=300, deadline=None)
    def test_always_terminates(self, instrs: list[str], seed: int) -> None:
        """Every generated program halts or faults (never hangs)."""
        source = build_program(instrs, seed)
        result = assemble(source)
        cpu = CPU()
        cpu.load(result.code)
        state = cpu.run(max_steps=10000)
        assert state in (CpuState.HALTED, CpuState.FAULT)

    @given(instrs=_int_instrs, seed=_seed)
    @settings(max_examples=300, deadline=None)
    def test_registers_8bit(self, instrs: list[str], seed: int) -> None:
        """All GPR values are 0-255 after execution."""
        source = build_program(instrs, seed)
        cpu = run(source)
        for name in ("a", "b", "c", "d"):
            val = getattr(cpu, name)
            assert 0 <= val <= 255, f"reg {name} = {val}"

    @given(instrs=_int_instrs, seed=_seed)
    @settings(max_examples=300, deadline=None)
    def test_sp_in_range(self, instrs: list[str], seed: int) -> None:
        """SP is in valid range after execution."""
        source = build_program(instrs, seed)
        cpu = run(source)
        if cpu.state == CpuState.HALTED:
            assert 0 <= cpu.sp <= SP_INIT, f"SP = {cpu.sp}"

    @given(instrs=_int_instrs, seed=_seed)
    @settings(max_examples=300, deadline=None)
    def test_cycles_ge_steps(self, instrs: list[str], seed: int) -> None:
        """Total cycles >= total steps (every instruction costs >= 1)."""
        source = build_program(instrs, seed)
        cpu = run(source)
        assert cpu.cycles >= cpu.steps

    @given(instrs=_int_instrs, seed=_seed)
    @settings(max_examples=200, deadline=None)
    def test_halted_no_fault_flag(self, instrs: list[str], seed: int) -> None:
        """HALTED state has fault flag cleared."""
        source = build_program(instrs, seed)
        cpu = run(source)
        if cpu.state == CpuState.HALTED:
            assert not cpu.regs.flags.f

    @given(instrs=_int_instrs, seed=_seed)
    @settings(max_examples=200, deadline=None)
    def test_peak_mem_nonnegative(self, instrs: list[str], seed: int) -> None:
        """peak_mem is always >= 0."""
        source = build_program(instrs, seed)
        cpu = run(source)
        assert cpu.peak_mem >= 0


class TestFpInvariants:
    """Structural invariants for FP programs."""

    @given(instrs=_fp_instrs, seed=_seed)
    @settings(max_examples=200, deadline=None)
    def test_fp_always_terminates(self, instrs: list[str], seed: int) -> None:
        """FP programs halt or fault."""
        source = build_program(instrs, seed, arch=2)
        result = assemble(source, arch=2)
        cpu = CPU(arch=2)
        cpu.load(result.code)
        state = cpu.run(max_steps=10000)
        assert state in (CpuState.HALTED, CpuState.FAULT)

    @given(instrs=_fp_instrs, seed=_seed)
    @settings(max_examples=200, deadline=None)
    def test_fpsr_valid_bits(self, instrs: list[str], seed: int) -> None:
        """FPSR only has valid exception bits set (bits 0-4)."""
        source = build_program(instrs, seed, arch=2)
        cpu = run(source, arch=2)
        if cpu.state == CpuState.HALTED and cpu.regs.fpu is not None:
            assert cpu.regs.fpu.fpsr & ~0x1F == 0, f"FPSR = 0x{cpu.regs.fpu.fpsr:02X}"

    @given(instrs=_fp_instrs, seed=_seed)
    @settings(max_examples=200, deadline=None)
    def test_fpcr_valid_bits(self, instrs: list[str], seed: int) -> None:
        """FPCR only has rounding mode bits set (bits 0-1)."""
        source = build_program(instrs, seed, arch=2)
        cpu = run(source, arch=2)
        if cpu.state == CpuState.HALTED and cpu.regs.fpu is not None:
            assert cpu.regs.fpu.fpcr & ~0x03 == 0, f"FPCR = 0x{cpu.regs.fpu.fpcr:02X}"
