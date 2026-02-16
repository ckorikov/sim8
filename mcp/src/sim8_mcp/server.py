"""FastMCP server exposing sim8 assembler, simulator, and disassembler."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from fastmcp import FastMCP

from pysim8.asm import assemble
from pysim8.asm.parser import AsmError
from pysim8.disasm import disasm
from pysim8.sim import CPU, CpuState

mcp = FastMCP("sim8")

SPEC_SECTIONS = frozenset({
    "isa", "opcodes", "errors", "cpu", "mem", "uarch", "asm", "spec", "tests",
})


def _find_spec_dir() -> Path:
    """Find spec/ by walking up from this file."""
    for parent in Path(__file__).resolve().parents:
        candidate = parent / "spec"
        if (candidate / "isa.md").is_file():
            return candidate
    raise FileNotFoundError("spec/ directory not found in any parent")


SPEC_DIR = _find_spec_dir()


def _parse_hex(code_hex: str) -> list[int] | str:
    """Parse hex string into byte list. Returns error string on failure."""
    try:
        return list(bytes.fromhex(code_hex))
    except ValueError as e:
        return f"invalid hex: {e}"


def _cpu_state(cpu: CPU) -> dict[str, Any]:
    """Serialize CPU state to a JSON-friendly dict."""
    r = cpu.regs
    return {
        "state": cpu.state.value,
        "registers": {
            "A": r.a, "B": r.b, "C": r.c, "D": r.d,
            "SP": r.sp, "DP": r.dp, "IP": r.ip,
        },
        "flags": {"Z": r.flags.z, "C": r.flags.c, "F": r.flags.f},
        "display": cpu.display(),
    }


def _run_cpu(code: list[int], max_steps: int) -> dict[str, Any]:
    """Load code into CPU, run, return state dict."""
    cpu = CPU()
    try:
        cpu.load(code)
    except ValueError as e:
        return {"error": str(e)}
    cpu.run(max_steps)
    result = _cpu_state(cpu)
    if cpu.state == CpuState.RUNNING:
        result["warning"] = (
            f"step limit ({max_steps}) reached — possible infinite loop"
        )
    return result


@mcp.tool()
def assemble_source(source: str) -> dict[str, Any]:
    """Assemble source code into machine code.

    Args:
        source: Assembly source text.

    Returns:
        Dict with code_hex, labels, and mapping (code position -> source line).
    """
    try:
        result = assemble(source)
    except AsmError as e:
        return {"error": f"line {e.line}: {e.message}"}
    return {
        "code_hex": bytes(result.code).hex(),
        "labels": result.labels,
        "mapping": {str(k): v for k, v in result.mapping.items()},
    }


@mcp.tool()
def run_program(source: str, max_steps: int = 100_000) -> dict[str, Any]:
    """Assemble source code and run the program to completion.

    Args:
        source: Assembly source text.
        max_steps: Maximum number of CPU steps before stopping.

    Returns:
        Final CPU state (registers, flags, display) or assembler error.
    """
    try:
        result = assemble(source)
    except AsmError as e:
        return {"error": f"line {e.line}: {e.message}"}
    return _run_cpu(result.code, max_steps)


@mcp.tool()
def run_binary(code_hex: str, max_steps: int = 100_000) -> dict[str, Any]:
    """Run a pre-assembled binary.

    Args:
        code_hex: Hex-encoded machine code bytes.
        max_steps: Maximum number of CPU steps before stopping.

    Returns:
        Final CPU state (registers, flags, display).
    """
    parsed = _parse_hex(code_hex)
    if isinstance(parsed, str):
        return {"error": parsed}
    return _run_cpu(parsed, max_steps)


@mcp.tool()
def disassemble(code_hex: str) -> dict[str, Any]:
    """Disassemble hex-encoded machine code.

    Args:
        code_hex: Hex-encoded machine code bytes.

    Returns:
        List of instructions with address, text, and size.
    """
    parsed = _parse_hex(code_hex)
    if isinstance(parsed, str):
        return {"error": parsed}
    entries = disasm(parsed)
    return {
        "instructions": [
            {"address": addr, "text": text, "size": size}
            for addr, text, size in entries
        ],
    }


@mcp.tool()
def get_spec(section: str) -> dict[str, Any]:
    """Get a section of the CPU specification.

    Args:
        section: Section name (one of: isa, opcodes, errors, cpu, mem, uarch, asm, spec, tests).

    Returns:
        Markdown content of the specification section.
    """
    if section not in SPEC_SECTIONS:
        return {"error": f"unknown section: {section}. Valid: {sorted(SPEC_SECTIONS)}"}
    path = SPEC_DIR / f"{section}.md"
    if not path.is_file():
        return {"error": f"spec file not found: {section}.md"}
    return {"content": path.read_text(encoding="utf-8")}
