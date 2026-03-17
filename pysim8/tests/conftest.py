"""Shared test helpers for assembler tests."""

from __future__ import annotations

import pytest

from pysim8.asm import AssemblerError, assemble


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
