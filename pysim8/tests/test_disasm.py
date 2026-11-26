"""Tests for the disassembler — roundtrip asm ↔ disasm."""

from pathlib import Path

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from pysim8.asm import assemble
from pysim8.disasm import disasm, disasm_insn
from pysim8.isa import (
    FP_FMT_BF,
    FP_FMT_F,
    FP_FMT_H,
    FP_FMT_O2,
    FP_FMT_O3,
    ISA,
    InstrDef,
    Op,
    OpType,
    encode_fpm,
)

# Sample operand values per (position, operand_type).
_SAMPLES: dict[tuple[int, OpType], int] = {
    (0, OpType.REG): 2,
    (0, OpType.REG_ARITH): 0,
    (0, OpType.REG_STACK): 1,
    (0, OpType.REG_GPR): 1,
    (0, OpType.IMM): 42,
    (0, OpType.MEM): 100,
    (0, OpType.REGADDR): (3 << 3) | 2,
    (1, OpType.REG): 3,
    (1, OpType.REG_ARITH): 4,
    (1, OpType.REG_GPR): 3,
    (1, OpType.IMM): 99,
    (1, OpType.MEM): 200,
    (1, OpType.REGADDR): (5 << 3) | 1,
}


def _make_operands(defn: InstrDef) -> tuple[int, ...]:
    return tuple(_SAMPLES[i, ot] for i, ot in enumerate(defn.sig))


# ── Roundtrip: assemble(disasm(bytes)) == bytes ──────────────────────


@pytest.mark.parametrize("defn", ISA, ids=lambda d: d.op.name)
def test_roundtrip(defn: InstrDef) -> None:
    operands = _make_operands(defn)
    original = [int(defn.op)] + list(operands)

    text = disasm_insn(int(defn.op), operands)
    result = assemble(text + "\nHLT")

    assert result.code[: defn.size] == original, (
        f"{defn.op.name}: disasm={text!r}, expected={original}, got={result.code[: defn.size]}"
    )


# ── Edge cases ───────────────────────────────────────────────────────


def test_unknown_opcode() -> None:
    code = [9, 42]
    items = disasm(code)
    assert items == [(0, "DB 9", 1), (1, "DB 42", 1)]


def test_truncated_instruction() -> None:
    code = [6, 0]
    items = disasm(code)
    assert items[0] == (0, "DB 6", 1)


def test_full_stream() -> None:
    code = [6, 0, 42, 18, 0, 0]
    items = disasm(code)

    assert len(items) == 3
    assert items[0] == (0, "MOV A, 42", 3)
    assert items[1] == (3, "INC A", 2)
    assert items[2] == (5, "HLT", 1)

    assert sum(sz for _, _, sz in items) == len(code)


def test_disasm_insn_unknown() -> None:
    assert disasm_insn(255) == "??? (255)"


def test_fmt_operand_unknown_type() -> None:
    from pysim8.disasm.core import _fmt_operand

    with pytest.raises(ValueError, match="unknown operand type"):
        _fmt_operand(OpType.FP_REG, 0)


# ── REGADDR encoding roundtrip ───────────────────────────────────────


@pytest.mark.parametrize(
    "reg,offset,expected",
    [
        (0, 0, "[A]"),
        (1, 3, "[B+3]"),
        (2, -2, "[C-2]"),
        (3, 15, "[D+15]"),
        (0, -16, "[A-16]"),
    ],
)
def test_regaddr_disasm(reg: int, offset: int, expected: str) -> None:
    offset_u = offset if offset >= 0 else 32 + offset
    encoded = (offset_u << 3) | reg
    text = disasm_insn(3, (0, encoded))
    assert expected in text


@pytest.mark.parametrize("offset", [0, 1, 5, 15, -1, -5, -16])
def test_regaddr_roundtrip(offset: int) -> None:
    """assemble → disasm → assemble for REGADDR with various offsets."""
    sign = f"+{offset}" if offset > 0 else str(offset)
    suffix = sign if offset != 0 else ""
    source = f"MOV A, [B{suffix}]\nHLT"
    code = assemble(source).code
    text = disasm_insn(code[0], (code[1], code[2]))
    reassembled = assemble(text + "\nHLT").code[:3]
    assert reassembled == code[:3]


# ── Disasm CLI ────────────────────────────────────────────────────


def test_disasm_cli(tmp_path: Path) -> None:
    """Full CLI path for disassembler."""
    from click.testing import CliRunner

    from pysim8.disasm.cli import main

    bin_file = tmp_path / "test.bin"
    bin_file.write_bytes(bytes([6, 0, 42, 0]))
    runner = CliRunner()
    result = runner.invoke(main, [str(bin_file)])
    assert result.exit_code == 0
    assert "MOV" in result.output


# ── FP disassembly ─────────────────────────────────────────────────────


class TestFpDisasm:
    """FP instruction disassembly."""

    def test_fadd_addr(self) -> None:
        fpm = encode_fpm(0, 0, FP_FMT_H)
        text = disasm_insn(int(Op.FADD_FP_ADDR), (fpm, 100))
        assert text == "FADD.H FHA, [100]"

    def test_fabs(self) -> None:
        fpm = encode_fpm(0, 0, FP_FMT_F)
        text = disasm_insn(int(Op.FABS_FP), (fpm,))
        assert text == "FABS.F FA"

    def test_fneg(self) -> None:
        fpm = encode_fpm(1, 0, FP_FMT_F)
        text = disasm_insn(int(Op.FNEG_FP), (fpm,))
        assert text == "FNEG.F FB"

    def test_fsqrt(self) -> None:
        fpm = encode_fpm(0, 1, FP_FMT_O3)
        text = disasm_insn(int(Op.FSQRT_FP), (fpm,))
        assert text == "FSQRT.O3 FQB"

    def test_fmov_rr(self) -> None:
        dst = encode_fpm(0, 0, FP_FMT_H)
        src = encode_fpm(0, 1, FP_FMT_H)
        text = disasm_insn(int(Op.FMOV_RR), (dst, src))
        assert text == "FMOV.H FHA, FHB"

    def test_fcvt_dual_suffix(self) -> None:
        dst = encode_fpm(0, 0, FP_FMT_H)
        src = encode_fpm(0, 0, FP_FMT_F)
        text = disasm_insn(int(Op.FCVT_FP_FP), (dst, src))
        assert text == "FCVT.H.F FHA, FA"

    def test_fcvt_same_suffix(self) -> None:
        """Same format → single suffix (pathological, but valid encoding)."""
        dst = encode_fpm(0, 0, FP_FMT_H)
        src = encode_fpm(0, 1, FP_FMT_H)
        text = disasm_insn(int(Op.FCVT_FP_FP), (dst, src))
        assert text == "FCVT.H FHA, FHB"

    def test_fitof(self) -> None:
        fpm = encode_fpm(0, 0, FP_FMT_H)
        text = disasm_insn(int(Op.FITOF_FP_GPR), (fpm, 1))
        assert text == "FITOF.H FHA, B"

    def test_fftoi(self) -> None:
        """FFTOI encoding: [opcode, FPM, GPR] but display: FFTOI.H GPR, FP."""
        fpm = encode_fpm(0, 0, FP_FMT_H)
        text = disasm_insn(int(Op.FFTOI_GPR_FP), (fpm, 1))
        assert text == "FFTOI.H B, FHA"

    def test_fstat_control(self) -> None:
        text = disasm_insn(int(Op.FSTAT_GPR), (1,))
        assert text == "FSTAT B"

    def test_fclr_control(self) -> None:
        text = disasm_insn(int(Op.FCLR), ())
        assert text == "FCLR"

    def test_fscfg_control(self) -> None:
        text = disasm_insn(int(Op.FSCFG_GPR), (2,))
        assert text == "FSCFG C"

    def test_fmov_imm8(self) -> None:
        fpm = encode_fpm(0, 0, FP_FMT_O3)
        text = disasm_insn(int(Op.FMOV_FP_IMM8), (fpm, 42))
        assert text == "FMOV.O3 FQA, 0.3125_O3"

    def test_fmov_imm16(self) -> None:
        fpm = encode_fpm(0, 0, FP_FMT_H)
        text = disasm_insn(int(Op.FMOV_FP_IMM16), (fpm, 0x00, 0x3C))
        assert text == "FMOV.H FHA, 1_H"

    def test_fmadd(self) -> None:
        dst = encode_fpm(0, 0, FP_FMT_H)
        src = encode_fpm(0, 1, FP_FMT_H)
        text = disasm_insn(int(Op.FMADD_FP_FP_ADDR), (dst, src, 100))
        assert text == "FMADD.H FHA, FHB, [100]"

    def test_fadd_regaddr(self) -> None:
        fpm = encode_fpm(0, 0, FP_FMT_BF)
        ra = (3 << 3) | 1
        text = disasm_insn(int(Op.FADD_FP_REGADDR), (fpm, ra))
        assert "FADD.BF" in text
        assert "[B+3]" in text

    def test_fp_in_disasm_stream(self) -> None:
        """FP opcodes in a byte stream are decoded, not treated as DB."""
        fpm = encode_fpm(0, 0, FP_FMT_F)
        code = [int(Op.FABS_FP), fpm, 0]
        items = disasm(code)
        assert len(items) == 2
        assert items[0] == (0, "FABS.F FA", 2)
        assert items[1] == (2, "HLT", 1)

    def test_fp_truncated_in_stream(self) -> None:
        """Truncated FP instruction → DB fallback."""
        code = [int(Op.FADD_FP_ADDR)]
        items = disasm(code)
        assert items[0][1].startswith("DB")

    def test_all_fp_formats(self) -> None:
        """Every FP format suffix is recognized."""
        for fmt, suffix in [
            (FP_FMT_F, "F"),
            (FP_FMT_H, "H"),
            (FP_FMT_BF, "BF"),
            (FP_FMT_O3, "O3"),
            (FP_FMT_O2, "O2"),
        ]:
            fpm = encode_fpm(0, 0, fmt)
            text = disasm_insn(int(Op.FABS_FP), (fpm,))
            assert f".{suffix}" in text

    def test_phys1_register(self) -> None:
        """Physical register 1 names (FB family)."""
        fpm = encode_fpm(1, 0, FP_FMT_F)
        text = disasm_insn(int(Op.FABS_FP), (fpm,))
        assert text == "FABS.F FB"


class TestBuildFpmToReg:
    """Tests for _build_fpm_to_reg — shortest-name selection."""

    def test_shorter_name_wins(self) -> None:
        """When two names share a key, the shorter one wins."""
        from pysim8.disasm.core import _build_fpm_to_reg

        regs = {
            "LONGER": (0, 0, 0, 32),
            "SH": (0, 0, 0, 32),
        }
        result = _build_fpm_to_reg(regs)
        assert result[(0, 0, 0)] == "SH"

    def test_first_seen_kept_if_same_length(self) -> None:
        from pysim8.disasm.core import _build_fpm_to_reg

        regs = {
            "AA": (0, 0, 1, 16),
            "BB": (0, 0, 1, 16),
        }
        result = _build_fpm_to_reg(regs)
        assert result[(0, 0, 1)] == "AA"

    def test_unique_keys(self) -> None:
        from pysim8.disasm.core import _build_fpm_to_reg

        regs = {
            "X": (0, 0, 0, 8),
            "Y": (1, 0, 0, 8),
        }
        result = _build_fpm_to_reg(regs)
        assert result[(0, 0, 0)] == "X"
        assert result[(1, 0, 0)] == "Y"


class TestDisasmFpEdgeCoverage:
    """Tests for disasm/core.py uncovered lines 129, 133."""

    def test_fp_data_no_fpreg_operands(self) -> None:
        """FP data instr with zero FP_REG operands → label without suffix."""
        from pysim8.disasm.core import _disasm_fp_insn
        from pysim8.isa import BY_CODE_FP, InstrDef, Op, OpType

        fake = InstrDef(Op.FCLR, "FTEST", (OpType.MEM,), cost=1)
        saved = BY_CODE_FP.get(int(Op.FCLR))
        BY_CODE_FP[int(Op.FCLR)] = fake
        try:
            result = _disasm_fp_insn(int(Op.FCLR), (42,))
            assert result == "FTEST [42]"
        finally:
            if saved is not None:
                BY_CODE_FP[int(Op.FCLR)] = saved
            else:
                del BY_CODE_FP[int(Op.FCLR)]

    def test_fp_data_no_operands(self) -> None:
        """FP data instr with zero operands → bare label."""
        from pysim8.disasm.core import _disasm_fp_insn
        from pysim8.isa import BY_CODE_FP, InstrDef, Op

        fake = InstrDef(Op.FCLR, "FBARE", (), cost=1)
        saved = BY_CODE_FP.get(int(Op.FCLR))
        BY_CODE_FP[int(Op.FCLR)] = fake
        try:
            result = _disasm_fp_insn(int(Op.FCLR), ())
            assert result == "FBARE"
        finally:
            if saved is not None:
                BY_CODE_FP[int(Op.FCLR)] = saved
            else:
                del BY_CODE_FP[int(Op.FCLR)]


# ── Hypothesis property-based tests ──────────────────────────────────


class TestDisasmProperties:
    """Property-based tests for disassembler robustness."""

    @given(code=st.lists(st.integers(0, 255), min_size=1, max_size=100))
    @settings(max_examples=500)
    def test_never_crashes(self, code: list[int]) -> None:
        """Disasm must not crash on arbitrary bytecode."""
        items = disasm(code)
        assert isinstance(items, list)
        for addr, text, sz in items:
            assert isinstance(addr, int)
            assert isinstance(text, str)
            assert isinstance(sz, int)
            assert sz >= 1

    @given(code=st.lists(st.integers(0, 255), min_size=1, max_size=100))
    @settings(max_examples=300)
    def test_sizes_cover_input(self, code: list[int]) -> None:
        """Sum of disassembled instruction sizes == input length."""
        items = disasm(code)
        total = sum(sz for _, _, sz in items)
        assert total == len(code)

    @given(code=st.lists(st.integers(0, 255), min_size=1, max_size=100))
    @settings(max_examples=300)
    def test_addresses_sequential(self, code: list[int]) -> None:
        """Addresses are strictly ascending and contiguous."""
        items = disasm(code)
        if not items:
            return
        assert items[0][0] == 0
        for i in range(1, len(items)):
            prev_addr, _, prev_sz = items[i - 1]
            assert items[i][0] == prev_addr + prev_sz
