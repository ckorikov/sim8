"""Tests for sim8 MCP server tools."""

from __future__ import annotations

import asyncio

import sim8_mcp.server as srv

# Import plain logic functions directly — no FastMCP internals needed.
assemble_source = srv.tool_assemble_source
run_program = srv.tool_run_program
run_binary = srv.tool_run_binary
disassemble = srv.tool_disassemble
get_spec = srv.tool_get_spec
search_spec = srv.tool_search_spec
describe_instr = srv.tool_describe_instr
list_instructions = srv.tool_list_instructions


# ── MCP registration ─────────────────────────────────────────────


def test_mcp_tools_registered() -> None:
    tools = asyncio.run(srv.mcp._tool_manager.get_tools())
    expected = {
        "assemble_source",
        "run_program",
        "run_binary",
        "disassemble",
        "get_spec",
        "search_spec",
        "describe_instr",
        "list_instructions",
    }
    assert expected == set(tools.keys())


# ── assemble_source ───────────────────────────────────────────────


def test_assemble_simple() -> None:
    result = assemble_source("MOV A, 42\nHLT")
    assert "error" not in result
    assert isinstance(result["code_hex"], str)
    assert len(result["code_hex"]) > 0
    assert isinstance(result["labels"], dict)
    assert isinstance(result["mapping"], dict)


def test_assemble_with_label() -> None:
    result = assemble_source("start:\nMOV A, 1\nJMP start")
    assert "error" not in result
    assert "start" in result["labels"]
    assert result["labels"]["start"] == 0


def test_assemble_error() -> None:
    result = assemble_source("INVALID_OP")
    assert "error" in result


def test_assemble_with_include() -> None:
    """@include resolves against the repo filesystem and libs/ search path."""
    result = assemble_source('@include "std/io.str.asm"\nHLT')
    assert "error" not in result
    assert "print_str" in result["labels"]


# ── run_program ───────────────────────────────────────────────────


def test_run_program_with_include() -> None:
    """@include works end-to-end through run_program."""
    source = (
        "JMP start\n"
        '@include "std/io.str.asm"\n'
        "msg: DB 72, 105, 0\n"
        "start: MOV A, msg\n"
        "  MOV D, 232\n"
        "  CALL print_str\n"
        "  HLT"
    )
    result = run_program(source)
    assert result["state"] == "HALTED"
    assert result["display"].startswith("Hi")


def test_run_program_halts() -> None:
    result = run_program("MOV A, 42\nHLT")
    assert result["state"] == "HALTED"
    assert result["registers"]["A"] == 42


def test_run_program_asm_error() -> None:
    result = run_program("BAD_INSTRUCTION")
    assert "error" in result


def test_run_program_step_limit() -> None:
    result = run_program("loop:\nJMP loop", max_steps=10)
    assert result["state"] == "RUNNING"
    assert "warning" in result
    assert "error" not in result


def test_run_program_display() -> None:
    source = "MOV A, 72\nMOV [232], A\nHLT"
    result = run_program(source)
    assert result["state"] == "HALTED"
    assert result["display"] == "H"


def test_run_program_flags_zero() -> None:
    result = run_program("INC A\nDEC A\nHLT")
    assert result["state"] == "HALTED"
    assert result["flags"]["Z"] is True
    assert result["flags"]["F"] is False


def test_run_program_fault() -> None:
    result = run_program("MOV A, 10\nMOV B, 0\nDIV B\nHLT")
    assert result["state"] == "FAULT"
    assert result["flags"]["F"] is True


def test_run_program_fpu_state() -> None:
    result = run_program("FMOV.H FHA, 1.0\nHLT")
    assert result["state"] == "HALTED"
    assert "fpu" in result
    assert result["fpu"]["FA"] != 0
    assert "FPCR" in result["fpu"]
    assert "FPSR" in result["fpu"]


def test_assemble_fp_instruction() -> None:
    result = assemble_source("FADD.H FHA, FHB\nHLT")
    assert "error" not in result
    assert len(result["code_hex"]) > 0


# ── arch=1 (integer-only, no FPU) ─────────────────────────────────


def test_run_program_arch1_no_fpu() -> None:
    result = run_program("MOV A, 42\nHLT", arch=1)
    assert result["state"] == "HALTED"
    assert result["registers"]["A"] == 42
    assert "fpu" not in result


def test_assemble_arch1() -> None:
    result = assemble_source("MOV A, 1\nHLT", arch=1)
    assert "error" not in result


def test_run_binary_arch1() -> None:
    asm_result = assemble_source("MOV A, 5\nHLT", arch=1)
    assert "error" not in asm_result
    result = run_binary(asm_result["code_hex"], arch=1)
    assert result["state"] == "HALTED"
    assert result["registers"]["A"] == 5
    assert "fpu" not in result


# ── run_binary ────────────────────────────────────────────────────


def test_run_binary_halts() -> None:
    asm_result = assemble_source("MOV A, 7\nHLT")
    assert "error" not in asm_result
    result = run_binary(asm_result["code_hex"])
    assert result["state"] == "HALTED"
    assert result["registers"]["A"] == 7


def test_run_binary_invalid_hex() -> None:
    result = run_binary("ZZZZ")
    assert "error" in result


def test_run_binary_oversized() -> None:
    huge_hex = "00" * 65537
    result = run_binary(huge_hex)
    assert "error" in result


# ── disassemble ───────────────────────────────────────────────────


def test_disassemble_roundtrip() -> None:
    asm_result = assemble_source("MOV A, 42\nHLT")
    assert "error" not in asm_result
    dis_result = disassemble(asm_result["code_hex"])
    assert "error" not in dis_result
    instructions = dis_result["instructions"]
    assert all("address" in i and "text" in i and "size" in i for i in instructions)
    texts = [i["text"] for i in instructions]
    assert any("MOV" in t for t in texts)
    assert any("HLT" in t for t in texts)


def test_disassemble_invalid_hex() -> None:
    result = disassemble("GG")
    assert "error" in result


# ── get_spec ──────────────────────────────────────────────────────


def test_get_spec_valid() -> None:
    result = get_spec("isa")
    assert "error" not in result
    assert "content" in result
    assert len(result["content"]) > 0
    assert "total_lines" in result


def test_get_spec_invalid() -> None:
    result = get_spec("nonexistent")
    assert "error" in result


def test_get_spec_range() -> None:
    full = get_spec("isa")
    sliced = get_spec("isa", start_line=1, end_line=5)
    assert "error" not in sliced
    assert sliced["start_line"] == 1
    assert sliced["end_line"] == 5
    assert sliced["total_lines"] == full["total_lines"]
    assert len(sliced["content"].splitlines()) == 5


def test_get_spec_range_clamps_to_file() -> None:
    full = get_spec("cpu")
    total = full["total_lines"]
    result = get_spec("cpu", start_line=1, end_line=total + 999)
    assert result["end_line"] == total


def test_get_spec_fp_section() -> None:
    result = get_spec("fp")
    assert "error" not in result
    assert "content" in result


def test_get_spec_tests_not_exposed() -> None:
    assert "error" in get_spec("tests")
    assert "error" in get_spec("tests-fp")


# ── search_spec ───────────────────────────────────────────────────


def test_search_spec_finds_match() -> None:
    result = search_spec("MOV")
    assert "error" not in result
    assert result["total"] > 0
    assert all("section" in m and "line" in m and "text" in m for m in result["matches"])


def test_search_spec_section_filter() -> None:
    result = search_spec("register", section="isa")
    assert "error" not in result
    assert all(m["section"] == "isa" for m in result["matches"])


def test_search_spec_context_lines() -> None:
    result = search_spec("FAULT", section="errors", context=1)
    assert result["total"] > 0
    for m in result["matches"]:
        assert "context" in m
        assert len(m["context"]) <= 3  # 1 before + match + 1 after


def test_search_spec_no_match() -> None:
    result = search_spec("xyzzy_does_not_exist")
    assert result["total"] == 0
    assert result["matches"] == []


def test_search_spec_invalid_section() -> None:
    result = search_spec("foo", section="nonexistent")
    assert "error" in result


def test_search_spec_empty_query() -> None:
    result = search_spec("")
    assert "error" in result


# ── memory dump ──────────────────────────────────────────────────


def test_run_program_memory_dump() -> None:
    result = run_program("MOV A, 42\nMOV [100], A\nHLT", mem_start=100, mem_len=1)
    assert "error" not in result
    assert result["state"] == "HALTED"
    assert result["memory"]["start"] == 100
    assert result["memory"]["length"] == 1
    assert result["memory"]["bytes"] == [42]
    assert result["memory"]["hex"] == "2a"


def test_run_program_no_memory_by_default() -> None:
    result = run_program("HLT")
    assert "memory" not in result


def test_run_binary_memory_dump() -> None:
    asm_result = assemble_source("MOV A, 7\nMOV [50], A\nHLT")
    assert "error" not in asm_result
    result = run_binary(asm_result["code_hex"], mem_start=50, mem_len=2)
    assert result["memory"]["bytes"][0] == 7
    assert result["memory"]["length"] == 2


def test_run_program_memory_dump_page() -> None:
    """Dump a full page (default mem_len=256)."""
    result = run_program("MOV A, 0xFF\nMOV [0], A\nHLT", mem_start=0)
    assert result["memory"]["length"] == 256
    # byte at address 0 is the MOV opcode, not 0xFF (code is loaded there)
    assert len(result["memory"]["hex"]) == 512  # 256 bytes * 2 hex chars


def test_run_program_memory_invalid_start() -> None:
    result = run_program("HLT", mem_start=-1)
    assert "error" in result


def test_run_program_memory_invalid_len() -> None:
    result = run_program("HLT", mem_start=0, mem_len=0)
    assert "error" in result


# ── describe_instr ───────────────────────────────────────────────


def test_describe_instr_mov() -> None:
    result = describe_instr("MOV")
    assert "error" not in result
    assert result["mnemonic"] == "MOV"
    assert "Copy value" in result["description"]
    assert len(result["forms"]) > 0
    assert any("reg" in f for f in result["forms"])


def test_describe_instr_fadd() -> None:
    result = describe_instr("FADD")
    assert "error" not in result
    assert result["mnemonic"] == "FADD"
    assert "fp_exceptions" in result
    assert "fp_formats" in result


def test_describe_instr_alias() -> None:
    result = describe_instr("JB")
    assert "error" not in result
    assert result["mnemonic"] == "JC"
    assert result["alias_of"] == "JC"


def test_describe_instr_case_insensitive() -> None:
    result = describe_instr("mov")
    assert "error" not in result
    assert result["mnemonic"] == "MOV"


def test_describe_instr_unknown() -> None:
    result = describe_instr("XYZZY")
    assert "error" in result
    assert "mnemonics" in result
    assert "aliases" in result


def test_describe_instr_empty() -> None:
    result = describe_instr("")
    assert "error" in result


def test_describe_instr_fcontrol_no_formats() -> None:
    """FP control instructions (FSTAT, FCLR) should not show fp_formats."""
    result = describe_instr("FSTAT")
    assert "error" not in result
    assert "fp_formats" not in result


def test_describe_instr_flags() -> None:
    result = describe_instr("ADD")
    assert "flags" in result
    assert "Z" in result["flags"]


def test_describe_instr_note() -> None:
    result = describe_instr("DIV")
    assert "note" in result
    assert "FAULT" in result["note"]


# ── list_instructions ────────────────────────────────────────────


def test_list_instructions() -> None:
    result = list_instructions()
    assert "instructions" in result
    assert "aliases" in result
    mnemonics = [i["mnemonic"] for i in result["instructions"]]
    assert "MOV" in mnemonics
    assert "FADD" in mnemonics
    assert "HLT" in mnemonics
    assert len(result["aliases"]) > 0
    assert result["aliases"]["JB"] == "JC"
