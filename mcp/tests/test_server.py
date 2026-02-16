"""Tests for sim8 MCP server tools."""

from __future__ import annotations

import asyncio

import sim8_mcp.server as srv

# Access underlying functions through FunctionTool.fn
assemble_source = srv.assemble_source.fn
run_program = srv.run_program.fn
run_binary = srv.run_binary.fn
disassemble = srv.disassemble.fn
get_spec = srv.get_spec.fn


# ── MCP registration ─────────────────────────────────────────────


def test_mcp_tools_registered() -> None:
    tools = asyncio.run(srv.mcp._tool_manager.get_tools())
    expected = {"assemble_source", "run_program", "run_binary", "disassemble", "get_spec"}
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


# ── run_program ───────────────────────────────────────────────────


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


def test_get_spec_invalid() -> None:
    result = get_spec("nonexistent")
    assert "error" in result
