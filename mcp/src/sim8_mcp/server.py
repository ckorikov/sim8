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

SPEC_SECTIONS = frozenset(
    {
        "isa",
        "opcodes",
        "errors",
        "cpu",
        "mem",
        "uarch",
        "asm",
        "spec",
        "fp",
    }
)


def _find_repo_root() -> Path:
    """Find repo root (parent of spec/) by walking up from this file."""
    for parent in Path(__file__).resolve().parents:
        if (parent / "spec" / "isa.md").is_file():
            return parent
    raise FileNotFoundError("repo root not found (no spec/isa.md in any parent)")


REPO_ROOT = _find_repo_root()
SPEC_DIR = REPO_ROOT / "spec"
INCLUDE_PATHS = [REPO_ROOT / "libs"]


def _parse_hex(code_hex: str) -> list[int]:
    """Parse hex string into byte list. Raises ValueError on failure."""
    try:
        return list(bytes.fromhex(code_hex))
    except ValueError as e:
        raise ValueError(f"invalid hex: {e}") from e


def _cpu_state(cpu: CPU) -> dict[str, Any]:
    """Serialize CPU state to a JSON-friendly dict."""
    r = cpu.regs
    result: dict[str, Any] = {
        "state": cpu.state.value,
        "registers": {
            "A": r.a,
            "B": r.b,
            "C": r.c,
            "D": r.d,
            "SP": r.sp,
            "DP": r.dp,
            "IP": r.ip,
        },
        "flags": {"Z": r.flags.z, "C": r.flags.c, "F": r.flags.f},
        "display": cpu.display(),
    }
    if r.fpu is not None:
        result["fpu"] = {
            "FA": r.fpu.fa,
            "FB": r.fpu.fb,
            "FPCR": r.fpu.fpcr,
            "FPSR": r.fpu.fpsr,
        }
    return result


def _run_cpu(code: list[int], max_steps: int, arch: int = 2) -> dict[str, Any]:
    """Load code into CPU, run, return state dict."""
    cpu = CPU(arch=arch)
    try:
        cpu.load(code)
    except ValueError as e:
        return {"error": str(e)}
    cpu.run(max_steps)
    result = _cpu_state(cpu)
    if cpu.state == CpuState.RUNNING:
        result["warning"] = f"step limit ({max_steps}) reached — possible infinite loop"
    return result


# ── Tool implementations (plain functions, importable by tests) ───────────────


def tool_assemble_source(source: str, arch: int = 2) -> dict[str, Any]:
    """Assemble source code into machine code."""
    try:
        result = assemble(source, arch=arch, base_path=REPO_ROOT, include_paths=INCLUDE_PATHS)
    except AsmError as e:
        return {"error": str(e)}
    return {
        "code_hex": bytes(result.code).hex(),
        "labels": result.labels,
        "mapping": {str(k): v for k, v in result.mapping.items()},
    }


def tool_run_program(
    source: str,
    max_steps: int = 100_000,
    arch: int = 2,
) -> dict[str, Any]:
    """Assemble source code and run the program to completion."""
    try:
        result = assemble(source, arch=arch, base_path=REPO_ROOT, include_paths=INCLUDE_PATHS)
    except AsmError as e:
        return {"error": str(e)}
    return _run_cpu(result.code, max_steps, arch=arch)


def tool_run_binary(
    code_hex: str,
    max_steps: int = 100_000,
    arch: int = 2,
) -> dict[str, Any]:
    """Run a pre-assembled binary."""
    try:
        parsed = _parse_hex(code_hex)
    except ValueError as e:
        return {"error": str(e)}
    return _run_cpu(parsed, max_steps, arch=arch)


def tool_disassemble(code_hex: str) -> dict[str, Any]:
    """Disassemble hex-encoded machine code."""
    try:
        parsed = _parse_hex(code_hex)
    except ValueError as e:
        return {"error": str(e)}
    entries = disasm(parsed)
    return {
        "instructions": [{"address": addr, "text": text, "size": size} for addr, text, size in entries],
    }


def tool_get_spec(
    section: str,
    start_line: int | None = None,
    end_line: int | None = None,
) -> dict[str, Any]:
    """Get a section of the CPU specification, optionally sliced by line range."""
    if section not in SPEC_SECTIONS:
        return {"error": f"unknown section: {section}. Valid: {sorted(SPEC_SECTIONS)}"}
    path = SPEC_DIR / f"{section}.md"
    if not path.is_file():
        return {"error": f"spec file not found: {section}.md"}
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    total = len(lines)
    if start_line is None and end_line is None:
        return {"content": "".join(lines), "total_lines": total}
    lo = max(1, start_line or 1) - 1  # convert to 0-based
    hi = min(total, end_line or total)
    return {
        "content": "".join(lines[lo:hi]),
        "start_line": lo + 1,
        "end_line": hi,
        "total_lines": total,
    }


def tool_search_spec(
    query: str,
    section: str | None = None,
    context: int = 2,
) -> dict[str, Any]:
    """Search for a string across spec files, returning matching lines with context."""
    if not query:
        return {"error": "query must not be empty"}
    if section is not None and section not in SPEC_SECTIONS:
        return {"error": f"unknown section: {section}. Valid: {sorted(SPEC_SECTIONS)}"}

    sections_to_search = [section] if section else sorted(SPEC_SECTIONS)
    needle = query.lower()
    matches: list[dict[str, Any]] = []

    for sec in sections_to_search:
        path = SPEC_DIR / f"{sec}.md"
        if not path.is_file():
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if needle not in line.lower():
                continue
            lo = max(0, i - context)
            hi = min(len(lines), i + context + 1)
            matches.append(
                {
                    "section": sec,
                    "line": i + 1,  # 1-based
                    "text": line,
                    "context": lines[lo:hi],
                    "context_start_line": lo + 1,
                }
            )

    return {"matches": matches, "total": len(matches)}


# ── MCP tool registration ─────────────────────────────────────────────────────


@mcp.tool()
def assemble_source(source: str, arch: int = 2) -> dict[str, Any]:
    """Assemble source code into machine code.  Supports @include directives
    (resolved against the sim8 repository root).

    Args:
        source: Assembly source text.
        arch: Architecture version (1 = integer-only, 2 = with FPU). Default 2.

    Returns:
        Dict with code_hex, labels, and mapping (code byte offset -> [filename, line_no]).
    """
    return tool_assemble_source(source, arch)


@mcp.tool()
def run_program(
    source: str,
    max_steps: int = 100_000,
    arch: int = 2,
) -> dict[str, Any]:
    """Assemble source code and run the program to completion.
    Supports @include directives (resolved against the sim8 repository root).

    Args:
        source: Assembly source text.
        max_steps: Maximum number of CPU steps before stopping.
        arch: Architecture version (1 = integer-only, 2 = with FPU). Default 2.

    Returns:
        Final CPU state (registers, flags, display) or assembler error.
    """
    return tool_run_program(source, max_steps, arch)


@mcp.tool()
def run_binary(
    code_hex: str,
    max_steps: int = 100_000,
    arch: int = 2,
) -> dict[str, Any]:
    """Run a pre-assembled binary.

    Args:
        code_hex: Hex-encoded machine code bytes.
        max_steps: Maximum number of CPU steps before stopping.
        arch: Architecture version (1 = integer-only, 2 = with FPU). Default 2.

    Returns:
        Final CPU state (registers, flags, display).
    """
    return tool_run_binary(code_hex, max_steps, arch)


@mcp.tool()
def disassemble(code_hex: str) -> dict[str, Any]:
    """Disassemble hex-encoded machine code.

    Args:
        code_hex: Hex-encoded machine code bytes.

    Returns:
        List of instructions with address, text, and size.
    """
    return tool_disassemble(code_hex)


@mcp.tool()
def get_spec(
    section: str,
    start_line: int | None = None,
    end_line: int | None = None,
) -> dict[str, Any]:
    """Get a section of the CPU specification, optionally sliced by line range.

    Args:
        section: Section name (one of: isa, opcodes, errors, cpu, mem, uarch, asm, spec, fp).
        start_line: First line to return (1-based, inclusive). Default: start of file.
        end_line: Last line to return (1-based, inclusive). Default: end of file.

    Returns:
        Markdown content, with total_lines and the actual range returned when sliced.
        Use total_lines to plan subsequent range reads for large sections.
    """
    return tool_get_spec(section, start_line, end_line)


@mcp.tool()
def search_spec(
    query: str,
    section: str | None = None,
    context: int = 2,
) -> dict[str, Any]:
    """Search for a string across spec files.

    Args:
        query: Case-insensitive substring to search for.
        section: Limit search to one section. Default: search all sections.
        context: Number of surrounding lines to include with each match. Default: 2.

    Returns:
        List of matches with section name, line number, matched text, and context lines.
        Use the line numbers with get_spec(section, start_line, end_line) to read more.
    """
    return tool_search_spec(query, section, context)
