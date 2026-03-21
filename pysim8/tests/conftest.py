"""Shared test helpers for assembler and simulator tests."""

from __future__ import annotations

import pytest

from pysim8.asm import AssemblerError, assemble
from pysim8.sim import CPU, CpuState


def run(source: str, arch: int = 1) -> CPU:
    """Assemble source, load into CPU, run until halt/fault."""
    result = assemble(source, arch=arch)
    cpu = CPU(arch=arch)
    cpu.load(result.code)
    state = cpu.run()
    assert state != CpuState.RUNNING, "Step limit reached — infinite loop?"
    return cpu


def asm_bytes(source: str, arch: int = 2) -> list[int]:
    """Assemble and return machine code bytes."""
    return assemble(source, arch=arch).code


def asm_labels(source: str, arch: int = 2) -> dict[str, int]:
    """Assemble and return label table."""
    return assemble(source, arch=arch).labels


def asm_mapping(source: str, arch: int = 2) -> dict[int, int]:
    """Assemble and return source mapping."""
    return assemble(source, arch=arch).mapping


def asm_error(source: str, arch: int = 2) -> AssemblerError:
    """Assemble expecting an error; return the exception."""
    with pytest.raises(AssemblerError) as exc_info:
        assemble(source, arch=arch)
    return exc_info.value
