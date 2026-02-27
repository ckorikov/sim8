"""Tests for the disassembler — roundtrip asm ↔ disasm."""

import pytest

from pysim8.asm import assemble
from pysim8.disasm import disasm, disasm_insn
from pysim8.isa import ISA, InsnDef, OpType

# Sample operand values per (position, operand_type).
_SAMPLES: dict[tuple[int, OpType], int] = {
    (0, OpType.REG): 2,        # C
    (0, OpType.REG_STACK): 0,  # A
    (0, OpType.REG_GPR): 1,    # B
    (0, OpType.IMM): 42,
    (0, OpType.MEM): 100,
    (0, OpType.REGADDR): (3 << 3) | 2,  # [C+3]
    (1, OpType.REG): 3,                  # D
    (1, OpType.REG_STACK): 4,            # SP
    (1, OpType.REG_GPR): 3,              # D
    (1, OpType.IMM): 99,
    (1, OpType.MEM): 200,
    (1, OpType.REGADDR): (5 << 3) | 1,  # [B+5]
}


def _make_operands(defn: InsnDef) -> tuple[int, ...]:
    return tuple(_SAMPLES[i, ot] for i, ot in enumerate(defn.sig))


# ── Roundtrip: assemble(disasm(bytes)) == bytes ──────────────────────


@pytest.mark.parametrize("defn", ISA, ids=lambda d: d.op.name)
def test_roundtrip(defn: InsnDef) -> None:
    operands = _make_operands(defn)
    original = [int(defn.op)] + list(operands)

    text = disasm_insn(int(defn.op), operands)
    result = assemble(text + "\nHLT")

    assert result.code[:defn.size] == original, (
        f"{defn.op.name}: disasm={text!r}, "
        f"expected={original}, got={result.code[:defn.size]}"
    )


# ── Edge cases ───────────────────────────────────────────────────────


def test_unknown_opcode() -> None:
    code = [9, 42]  # 9 is not a valid opcode
    items = disasm(code)
    assert items == [(0, "DB 9", 1), (1, "DB 42", 1)]


def test_truncated_instruction() -> None:
    code = [6, 0]  # MOV_REG_CONST needs 3 bytes, only 2 given
    items = disasm(code)
    assert items[0] == (0, "DB 6", 1)


def test_full_stream() -> None:
    # MOV A, 42 (3b) + INC A (2b) + HLT (1b)
    code = [6, 0, 42, 18, 0, 0]
    items = disasm(code)

    assert len(items) == 3
    assert items[0] == (0, "MOV A, 42", 3)
    assert items[1] == (3, "INC A", 2)
    assert items[2] == (5, "HLT", 1)

    # No gaps: total coverage
    assert sum(sz for _, _, sz in items) == len(code)


def test_disasm_insn_unknown() -> None:
    assert disasm_insn(255) == "??? (255)"


# ── REGADDR encoding roundtrip ───────────────────────────────────────


@pytest.mark.parametrize("reg,offset,expected", [
    (0, 0, "[A]"),
    (1, 3, "[B+3]"),
    (2, -2, "[C-2]"),
    (3, 15, "[D+15]"),
    (0, -16, "[A-16]"),
])
def test_regaddr_disasm(reg: int, offset: int, expected: str) -> None:
    offset_u = offset if offset >= 0 else 32 + offset
    encoded = (offset_u << 3) | reg
    # MOV_REG_REGADDR (opcode 3): MOV dest, [src±off]
    text = disasm_insn(3, (0, encoded))
    assert expected in text


@pytest.mark.parametrize("offset", [0, 1, 5, 15, -1, -5, -16])
def test_regaddr_roundtrip(offset: int) -> None:
    """assemble → disasm → assemble for REGADDR with various offsets."""
    sign = f"+{offset}" if offset > 0 else str(offset)
    suffix = sign if offset != 0 else ""
    source = f"MOV A, [B{suffix}]\nHLT"
    code = assemble(source).code
    # Disassemble and reassemble
    text = disasm_insn(code[0], (code[1], code[2]))
    reassembled = assemble(text + "\nHLT").code[:3]
    assert reassembled == code[:3]
