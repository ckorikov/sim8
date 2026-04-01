"""FastMCP server exposing sim8 assembler, simulator, and disassembler."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from fastmcp import FastMCP

from pysim8.asm import assemble
from pysim8.asm.parser import AsmError
from pysim8.disasm import disasm
from pysim8.isa import (
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    BY_MNEMONIC_VU,
    FP_CONTROL_MNEMONICS,
    ISA,
    ISA_FP,
    ISA_VU,
    MNEMONIC_ALIASES,
    MNEMONICS_FP,
    MNEMONICS_VU,
    OpType,
)
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
        "vector",
    }
)


# ── Instruction documentation (mirrors web/lib/isa-docs.js) ──────────────────

_SIG_LABELS: dict[str, str] = {
    OpType.REG.value: "reg",
    OpType.REG_ARITH.value: "reg|SP",
    OpType.REG_STACK.value: "gpr|DP",
    OpType.REG_GPR.value: "gpr",
    OpType.IMM.value: "imm",
    OpType.MEM.value: "[addr]",
    OpType.REGADDR.value: "regaddr",
    OpType.FP_REG.value: "fp",
    OpType.FP_IMM8.value: "imm8",
    OpType.FP_IMM16.value: "imm16",
}

_MNEMONIC_INFO: dict[str, str] = {
    "HLT": "Halt CPU execution",
    "MOV": "Copy value: reg, mem, or immediate",
    "ADD": "dest = dest + src; sets C, Z",
    "SUB": "dest = dest - src; sets C, Z",
    "INC": "dest = dest + 1; sets C, Z",
    "DEC": "dest = dest - 1; sets C, Z",
    "CMP": "dest - src (no store); Z=1 if equal, C=1 if src > dest",
    "MUL": "A = A * src; sets C, Z",
    "DIV": "A = A / src (integer); FAULT if src=0",
    "AND": "dest = dest & src; C=0, sets Z",
    "OR": "dest = dest | src; C=0, sets Z",
    "XOR": "dest = dest ^ src; C=0, sets Z",
    "NOT": "dest = ~dest; C=0, sets Z",
    "SHL": "dest = dest << n; sets C if overflow",
    "SHR": "dest = dest >>> n; sets C if bits lost",
    "JMP": "Unconditional jump",
    "JC": "Jump if C=1 (carry); after CMP: <",
    "JNC": "Jump if C=0 (no carry); after CMP: >=",
    "JZ": "Jump if Z=1 (zero); after CMP: ==",
    "JNZ": "Jump if Z=0 (not zero); after CMP: !=",
    "JA": "Jump if C=0 and Z=0 (above); after CMP: >",
    "JNA": "Jump if C=1 or Z=1 (not above); after CMP: <=",
    "PUSH": "Push to stack; SP--; FAULT if SP=0",
    "POP": "Pop from stack; SP++; FAULT if SP>=231",
    "CALL": "Push return addr, jump to target",
    "RET": "Pop addr from stack, jump to it",
    "DB": "Define raw byte(s), string, or FP data",
    "FMOV": "FP load/store or register copy",
    "FADD": "FP dst = dst + src",
    "FSUB": "FP dst = dst - src",
    "FMUL": "FP dst = dst * src",
    "FDIV": "FP dst = dst / src",
    "FCMP": "FP compare; sets Z, C (Z=C=1 if NaN)",
    "FABS": "Clear sign bit of FP register",
    "FNEG": "Toggle sign bit of FP register",
    "FSQRT": "FP square root",
    "FCVT": "Convert between FP formats",
    "FITOF": "uint8 GPR to FP register",
    "FFTOI": "FP to uint8 GPR (saturating)",
    "FSTAT": "Read FPSR (exception flags) to GPR",
    "FCFG": "Read FPCR (rounding mode) to GPR",
    "FSCFG": "Write GPR to FPCR (bits [1:0] only)",
    "FCLR": "Clear all FPSR sticky flags",
    "FCLASS": "Classify FP value to 8-bit bitmask",
    "FMADD": "FP dst = src * mem + dst (fused)",
    "VSET": "Set VU register (VA/VB/VC/VM/VL) from imm16, GPR pair, or memory",
    "VFSTAT": "Read VFPSR (vector FP exception flags) to GPR",
    "VFCLR": "Clear all VFPSR sticky flags",
    "VWAIT": "Wait for VU queue to drain; propagate VU faults to CPU",
    "VADD": "Vector dst = src1 + src2 (element-wise)",
    "VSUB": "Vector dst = src1 - src2 (element-wise)",
    "VMUL": "Vector dst = src1 * src2 (element-wise)",
    "VDIV": "Vector dst = src1 / src2 (element-wise)",
    "VMAX": "Vector dst = max(src1, src2) (element-wise)",
    "VMIN": "Vector dst = min(src1, src2) (element-wise)",
    "VDOT": "Vector dot product: dst += sum(src1 * src2)",
    "VSQRT": "Vector dst = sqrt(src1) (element-wise)",
    "VNEG": "Vector dst = -src1 (element-wise)",
    "VABS": "Vector dst = |src1| (element-wise)",
    "VCMP": "Vector compare src1, src2 → byte mask at [VM]",
    "VSEL": "Vector select: dst = mask ? src1 : dst",
    "VMOV": "Vector memory copy with auto-increment",
    "VFILL": "Vector fill dst with immediate value",
}

_MNEMONIC_FLAGS: dict[str, str] = {
    "ADD": "Z (result=0), C (unsigned overflow)",
    "SUB": "Z (result=0), C (borrow)",
    "INC": "Z (result=0), C (was 255)",
    "DEC": "Z (result=0), C (was 0)",
    "CMP": "Z=1 if equal; C=1 if a < b (unsigned)",
    "MUL": "Z (result=0), C (overflow)",
    "DIV": "Z (result=0), C=0",
    "AND": "Z (result=0), C=0",
    "OR": "Z (result=0), C=0",
    "XOR": "Z (result=0), C=0",
    "NOT": "Z (result=0), C=0",
    "SHL": "Z (result=0), C (last bit shifted out)",
    "SHR": "Z (result=0), C (last bit shifted out)",
    "FCMP": "Z, C (integer flags; Z=C=1 if unordered/NaN)",
}

_MNEMONIC_FP_EXCEPTIONS: dict[str, str] = {
    "FADD": "NV, OF, UF, NX",
    "FSUB": "NV, OF, UF, NX",
    "FMUL": "NV (0*Inf), OF, UF, NX",
    "FDIV": "NV (0/0, Inf/Inf), DZ (x/0), OF, UF, NX",
    "FCMP": "NV (sNaN)",
    "FSQRT": "NV (sqrt of negative or sNaN), NX",
    "FCVT": "NV (sNaN), OF, UF, NX",
    "FITOF": "NX",
    "FFTOI": "NV (NaN, +/-Inf), NX",
    "FMADD": "NV, DZ, OF, UF, NX",
}

_MNEMONIC_NOTES: dict[str, str] = {
    "DIV": "FAULT if divisor is zero (ERR_DIV_ZERO).",
    "PUSH": "FAULT if SP=0 (ERR_STACK_OVERFLOW).",
    "POP": "FAULT if SP>=231 (ERR_STACK_UNDERFLOW).",
    "JMP": "Target must be on page 0.",
    "CALL": "Target must be on page 0.",
    "FCVT": "Identical src/dst format is rejected — use FMOV instead.",
    "FSTAT": "FPSR bits: [0]=NV, [1]=DZ, [2]=OF, [3]=UF, [4]=NX.",
    "FCFG": "FPCR bits [1:0]: 00=RNE, 01=RTZ, 10=RDN, 11=RUP.",
    "FSCFG": "Only bits [1:0] are writable; reserved bits [7:2] are cleared.",
    "VWAIT": "Blocks CPU until VU queue is empty. If VU encountered a fault, CPU enters FAULT state.",
    "VDIV": "Integer div-by-zero (VDIV.I/.U) → FAULT(ERR_DIV_ZERO) deferred to VWAIT. FP div-by-zero sets VFPSR.DZ.",
    "VCMP": "Conditions: EQ(0), NE(1), LT(2), LE(3), GT(4), GE(5). Result is byte mask at [VM].",
    "VDOT": "FP-only (no .U/.I). dst gets scalar result (elem_size bytes). All three pointers auto-increment.",
}


def _build_instr_info(mnemonic: str) -> dict[str, Any] | None:
    """Build instruction info dict for a mnemonic."""
    canonical = MNEMONIC_ALIASES.get(mnemonic.upper(), mnemonic.upper())

    desc = _MNEMONIC_INFO.get(canonical)
    if desc is None:
        return None

    # Build syntax forms from ISA tables
    forms: list[str] = []
    seen: set[str] = set()
    for table in (BY_MNEMONIC, BY_MNEMONIC_FP, BY_MNEMONIC_VU):
        for instr_def in table.get(canonical, ()):
            sig = ", ".join(_SIG_LABELS.get(ot.value, "?") for ot in instr_def.sig)
            form = f"{instr_def.mnemonic} {sig}" if sig else instr_def.mnemonic
            if form not in seen:
                seen.add(form)
                forms.append(form)

    result: dict[str, Any] = {
        "mnemonic": canonical,
        "description": desc,
        "forms": forms,
    }

    if mnemonic.upper() != canonical:
        result["alias_of"] = canonical

    flags = _MNEMONIC_FLAGS.get(canonical)
    if flags:
        result["flags"] = flags

    fp_exc = _MNEMONIC_FP_EXCEPTIONS.get(canonical)
    if fp_exc:
        result["fp_exceptions"] = fp_exc

    if canonical in MNEMONICS_FP and canonical not in FP_CONTROL_MNEMONICS:
        result["fp_formats"] = ".F=float32, .H=float16, .BF=bfloat16, .O3=OFP8-E4M3, .O2=OFP8-E5M2"

    if canonical in MNEMONICS_VU:
        result["vu_formats"] = ".F=float32, .H=float16, .BF=bfloat16, .O3=OFP8-E4M3, .O2=OFP8-E5M2, .U=uint8, .I=int8"

    note = _MNEMONIC_NOTES.get(canonical)
    if note:
        result["note"] = note

    return result


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


def _read_memory(
    cpu: CPU,
    mem_start: int,
    mem_len: int,
) -> dict[str, Any]:
    """Read a contiguous range of CPU memory and return as hex + byte list."""
    end = min(mem_start + mem_len, 65536)
    actual_len = end - mem_start
    data = [cpu.mem[mem_start + i] for i in range(actual_len)]
    return {
        "start": mem_start,
        "length": actual_len,
        "hex": bytes(data).hex(),
        "bytes": data,
    }


def _run_cpu(
    code: list[int],
    max_steps: int,
    arch: int = 2,
    mem_start: int | None = None,
    mem_len: int = 256,
) -> dict[str, Any]:
    """Load code into CPU, run, return state dict."""
    if mem_start is not None:
        if not (0 <= mem_start < 65536):
            return {"error": f"mem_start must be 0..65535, got {mem_start}"}
        if mem_len < 1 or mem_len > 65536:
            return {"error": f"mem_len must be 1..65536, got {mem_len}"}
    cpu = CPU(arch=arch)
    try:
        cpu.load(code)
    except ValueError as e:
        return {"error": str(e)}
    effective_limit = max_steps if max_steps > 0 else 10_000_000
    cpu.run(effective_limit)
    result = _cpu_state(cpu)
    if cpu.state == CpuState.RUNNING:
        result["warning"] = f"step limit ({max_steps}) reached — possible infinite loop"
    if mem_start is not None:
        result["memory"] = _read_memory(cpu, mem_start, mem_len)
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
    max_steps: int = 0,
    arch: int = 2,
    mem_start: int | None = None,
    mem_len: int = 256,
) -> dict[str, Any]:
    """Assemble source code and run the program to completion."""
    try:
        result = assemble(source, arch=arch, base_path=REPO_ROOT, include_paths=INCLUDE_PATHS)
    except AsmError as e:
        return {"error": str(e)}
    return _run_cpu(result.code, max_steps, arch=arch, mem_start=mem_start, mem_len=mem_len)


def tool_run_binary(
    code_hex: str,
    max_steps: int = 0,
    arch: int = 2,
    mem_start: int | None = None,
    mem_len: int = 256,
) -> dict[str, Any]:
    """Run a pre-assembled binary."""
    try:
        parsed = _parse_hex(code_hex)
    except ValueError as e:
        return {"error": str(e)}
    return _run_cpu(parsed, max_steps, arch=arch, mem_start=mem_start, mem_len=mem_len)


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


def tool_describe_instr(mnemonic: str) -> dict[str, Any]:
    """Describe an instruction by mnemonic."""
    if not mnemonic:
        return {"error": "mnemonic must not be empty"}

    info = _build_instr_info(mnemonic)
    if info is not None:
        return info

    # Not found — list all available mnemonics
    all_mnemonics = sorted(
        {d.mnemonic for d in ISA} | {d.mnemonic for d in ISA_FP} | {d.mnemonic for d in ISA_VU} | {"DB"}
    )
    aliases = sorted(MNEMONIC_ALIASES.keys())
    return {
        "error": f"unknown mnemonic: {mnemonic.upper()}",
        "mnemonics": all_mnemonics,
        "aliases": aliases,
    }


def tool_list_instructions() -> dict[str, Any]:
    """List all instructions with brief descriptions."""
    result: list[dict[str, str]] = []
    for mn in sorted(_MNEMONIC_INFO):
        entry: dict[str, str] = {"mnemonic": mn, "description": _MNEMONIC_INFO[mn]}
        result.append(entry)
    aliases: dict[str, str] = {alias: canonical for alias, canonical in sorted(MNEMONIC_ALIASES.items())}
    return {"instructions": result, "aliases": aliases}


# ── MCP tool registration ─────────────────────────────────────────────────────


@mcp.tool()
def assemble_source(source: str, arch: int = 2) -> dict[str, Any]:
    """Assemble source code into machine code.  Supports @include directives
    (resolved against the sim8 repository root).

    Args:
        source: Assembly source text.
        arch: Architecture version (1 = integer-only, 2 = with FPU, 3 = FPU+VU). Default 2.

    Returns:
        Dict with code_hex, labels, and mapping (code byte offset -> [filename, line_no]).
    """
    return tool_assemble_source(source, arch)


@mcp.tool()
def run_program(
    source: str,
    max_steps: int = 0,
    arch: int = 2,
    mem_start: int | None = None,
    mem_len: int = 256,
) -> dict[str, Any]:
    """Assemble source code and run the program to completion.
    Supports @include directives (resolved against the sim8 repository root).

    Args:
        source: Assembly source text.
        max_steps: Maximum number of CPU steps before stopping. 0 = no limit (default).
        arch: Architecture version (1 = integer-only, 2 = with FPU, 3 = FPU+VU). Default 2.
        mem_start: If set, include a memory dump starting at this address (0-65535).
        mem_len: Number of bytes to dump (default 256, max 65536). Only used when mem_start is set.

    Returns:
        Final CPU state (registers, flags, display) or assembler error.
    """
    return tool_run_program(source, max_steps, arch, mem_start, mem_len)


@mcp.tool()
def run_binary(
    code_hex: str,
    max_steps: int = 0,
    arch: int = 2,
    mem_start: int | None = None,
    mem_len: int = 256,
) -> dict[str, Any]:
    """Run a pre-assembled binary.

    Args:
        code_hex: Hex-encoded machine code bytes.
        max_steps: Maximum number of CPU steps before stopping. 0 = no limit (default).
        arch: Architecture version (1 = integer-only, 2 = with FPU, 3 = FPU+VU). Default 2.
        mem_start: If set, include a memory dump starting at this address (0-65535).
        mem_len: Number of bytes to dump (default 256, max 65536). Only used when mem_start is set.

    Returns:
        Final CPU state (registers, flags, display).
    """
    return tool_run_binary(code_hex, max_steps, arch, mem_start, mem_len)


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
        section: Section name (one of: isa, opcodes, errors, cpu, mem, uarch, asm, spec, fp, vector).
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


@mcp.tool()
def describe_instr(mnemonic: str) -> dict[str, Any]:
    """Get detailed info about a CPU instruction: description, syntax forms, flags, FP exceptions, notes.

    Args:
        mnemonic: Instruction mnemonic (e.g. "MOV", "FADD", "JC"). Aliases like "JB", "JE" are resolved.

    Returns:
        Dict with mnemonic, description, syntax forms, flags, fp_exceptions, fp_formats, and notes.
        On unknown mnemonic, returns the full list of available mnemonics and aliases.
    """
    return tool_describe_instr(mnemonic)


@mcp.tool()
def list_instructions() -> dict[str, Any]:
    """List all sim8 instructions with brief descriptions and aliases.

    Returns:
        Dict with instructions (list of {mnemonic, description}) and aliases (alias -> canonical).
    """
    return tool_list_instructions()
