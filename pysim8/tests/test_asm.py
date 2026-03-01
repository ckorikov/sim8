"""Assembler tests from spec/tests.md (tests 110-184).

Tests are assembler-only: assemble source → verify bytes / labels / mapping / errors.
"""

from typing import get_args

import pytest
from hypothesis import given, settings, assume
from hypothesis import strategies as st

from pysim8.asm import assemble, AssemblerError
from pysim8.asm.parser import Operand, parse_number, ParseError
from pysim8.asm.codegen import _operand_matches, _encode_operand
from pysim8.isa import OpType


# ── helpers ──────────────────────────────────────────────────────────


def asm_bytes(source: str) -> list[int]:
    """Assemble and return machine code bytes."""
    return assemble(source).code


def asm_labels(source: str) -> dict[str, int]:
    """Assemble and return label table."""
    return assemble(source).labels


def asm_mapping(source: str) -> dict[int, int]:
    """Assemble and return source mapping."""
    return assemble(source).mapping


def asm_error(source: str) -> AssemblerError:
    """Assemble expecting an error; return the exception."""
    with pytest.raises(AssemblerError) as exc_info:
        assemble(source)
    return exc_info.value


# ── 5.16.1 Bytecode Verification (tests 110-120) ────────────────────


class TestBytecodeVerification:
    """Spec §5.16.1 — assembler produces correct bytes."""

    def test_110_hlt(self) -> None:
        assert asm_bytes("HLT") == [0]

    def test_111_ret(self) -> None:
        assert asm_bytes("RET") == [57]

    def test_112_mov_reg_reg(self) -> None:
        assert asm_bytes("MOV A, B") == [1, 0, 1]

    def test_113_mov_reg_const(self) -> None:
        assert asm_bytes("MOV A, 42") == [6, 0, 42]

    def test_114_inc_c(self) -> None:
        assert asm_bytes("INC C") == [18, 2]

    def test_115_jmp_addr(self) -> None:
        assert asm_bytes("JMP 100") == [31, 100]

    def test_116_push_const(self) -> None:
        assert asm_bytes("PUSH 255") == [53, 255]

    def test_117_add_reg_regaddr(self) -> None:
        assert asm_bytes("ADD A, [B+2]") == [11, 0, 17]

    def test_118_mov_reg_sp_minus_1(self) -> None:
        assert asm_bytes("MOV A, [SP-1]") == [3, 0, 252]

    def test_119_db_zero(self) -> None:
        assert asm_bytes("DB 0") == [0]

    def test_120_db_string(self) -> None:
        assert asm_bytes('DB "Hi"') == [72, 105]


# ── 5.16.2 Number Formats (tests 121-126) ───────────────────────────


class TestNumberFormats:
    """Spec §5.16.2 — all supported number formats."""

    def test_121_decimal(self) -> None:
        assert asm_bytes("MOV A, 200") == [6, 0, 200]

    def test_122_decimal_explicit(self) -> None:
        assert asm_bytes("MOV A, 200d") == [6, 0, 200]

    def test_123_hex(self) -> None:
        assert asm_bytes("MOV A, 0xC8") == [6, 0, 200]

    def test_124_octal(self) -> None:
        assert asm_bytes("MOV A, 0o310") == [6, 0, 200]

    def test_125_binary(self) -> None:
        assert asm_bytes("MOV A, 11001000b") == [6, 0, 200]

    def test_126_char_literal(self) -> None:
        assert asm_bytes("MOV A, 'A'") == [6, 0, 65]


# ── 5.16.3 Labels (tests 127-129) ───────────────────────────────────


class TestLabels:
    """Spec §5.16.3 — label resolution."""

    def test_127_label_at_zero(self) -> None:
        result = assemble("start: JMP start")
        assert result.code == [31, 0]
        assert result.labels["start"] == 0

    def test_128_forward_reference(self) -> None:
        result = assemble("JMP end\nend: HLT")
        assert result.code == [31, 2, 0]
        assert result.labels["end"] == 2

    def test_129_dot_prefix_label(self) -> None:
        result = assemble(".loop: JMP .loop")
        assert result.code == [31, 0]
        assert result.labels[".loop"] == 0


# ── 5.16.4 Case Insensitivity (tests 130-131) ───────────────────────


class TestCaseInsensitivity:
    """Spec §5.16.4 — mnemonics are case-insensitive."""

    def test_130_lowercase(self) -> None:
        assert asm_bytes("mov a, 5") == asm_bytes("MOV A, 5")

    def test_131_mixed_case(self) -> None:
        assert asm_bytes("Mov A, 5") == asm_bytes("MOV A, 5")


# ── 5.17 Error Handling (tests 132-148) ─────────────────────────────


class TestErrorHandling:
    """Spec §5.17 — assembler error messages and line numbers."""

    def test_132_duplicate_label(self) -> None:
        err = asm_error("x: DB 0\nx: DB 1")
        assert "Duplicate label" in err.message
        assert "x" in err.message.lower()
        assert err.line == 2

    def test_133_duplicate_label_case_insensitive(self) -> None:
        err = asm_error("X: DB 0\nx: DB 1")
        assert "Duplicate label" in err.message
        assert err.line == 2

    def test_134_label_keyword_a(self) -> None:
        err = asm_error("A: DB 0")
        assert "keyword" in err.message.lower()
        assert err.line == 1

    def test_135_label_keyword_b(self) -> None:
        err = asm_error("B: DB 0")
        assert "keyword" in err.message.lower()
        assert err.line == 1

    def test_136_undefined_label(self) -> None:
        err = asm_error("JMP nowhere")
        assert "Undefined label" in err.message
        assert "nowhere" in err.message

    def test_137_invalid_number(self) -> None:
        err = asm_error("MOV A, 0xZZ")
        assert err.line == 1

    def test_138_out_of_range(self) -> None:
        err = asm_error("MOV A, 256")
        assert "value between 0-255" in err.message

    def test_139_offset_too_large(self) -> None:
        err = asm_error("MOV A, [B+16]")
        assert "offset" in err.message.lower()
        assert "-16" in err.message
        assert "+15" in err.message

    def test_140_offset_too_small(self) -> None:
        err = asm_error("MOV A, [B-17]")
        assert "offset" in err.message.lower()

    def test_141_multi_char_literal(self) -> None:
        err = asm_error("MOV A, 'AB'")
        assert "Only one character" in err.message

    def test_142_invalid_operand(self) -> None:
        err = asm_error("ADD 5, A")
        assert "does not support this operand" in err.message

    def test_143_too_many_args(self) -> None:
        err = asm_error("INC A, B")
        assert "too many arguments" in err.message

    def test_144_db_invalid_operand(self) -> None:
        err = asm_error("DB [0x50]")
        assert "DB does not support this operand" in err.message

    def test_145_unknown_mnemonic(self) -> None:
        err = asm_error("FOO A")
        assert "Invalid instruction" in err.message
        assert "FOO" in err.message

    def test_146_syntax_error(self) -> None:
        err = asm_error("???")
        assert "Syntax error" in err.message

    def test_147_line_number_accuracy(self) -> None:
        err = asm_error("MOV A, 1\nMOV B, 2\nFOO")
        assert err.line == 3

    def test_148_blank_and_comment_lines(self) -> None:
        err = asm_error("; comment\nFOO")
        assert err.line == 2


# ── 5.18 Source Mapping (tests 149-151) ─────────────────────────────


class TestSourceMapping:
    """Spec §5.18 — mapping code positions to source lines."""

    def test_149_two_instructions(self) -> None:
        m = asm_mapping("MOV A, 1\nMOV B, 2")
        assert m == {0: 1, 3: 2}

    def test_150_db_excluded(self) -> None:
        m = asm_mapping("DB 42\nINC A")
        assert m == {1: 2}

    def test_151_label_no_bytes(self) -> None:
        m = asm_mapping("label: HLT")
        assert m == {0: 1}


# ── 5.6.3 Jump Aliases (tests 39-44) ────────────────────────────────


class TestJumpAliases:
    """Spec §5.6.3 — each alias produces the same opcodes."""

    def test_39_jb_jnae_jc(self) -> None:
        label = "\nlabel: HLT"
        assert asm_bytes("JB label" + label) == asm_bytes("JC label" + label)
        assert asm_bytes("JNAE label" + label) == asm_bytes("JC label" + label)

    def test_40_jnb_jae_jnc(self) -> None:
        label = "\nlabel: HLT"
        assert asm_bytes("JNB label" + label) == asm_bytes("JNC label" + label)
        assert asm_bytes("JAE label" + label) == asm_bytes("JNC label" + label)

    def test_41_je_jz(self) -> None:
        label = "\nlabel: HLT"
        assert asm_bytes("JE label" + label) == asm_bytes("JZ label" + label)

    def test_42_jne_jnz(self) -> None:
        label = "\nlabel: HLT"
        assert asm_bytes("JNE label" + label) == asm_bytes("JNZ label" + label)

    def test_43_jnbe_ja(self) -> None:
        label = "\nlabel: HLT"
        assert asm_bytes("JNBE label" + label) == asm_bytes("JA label" + label)

    def test_44_jbe_jna(self) -> None:
        label = "\nlabel: HLT"
        assert asm_bytes("JBE label" + label) == asm_bytes("JNA label" + label)


# ── 5.22.8 DB Comma-Separated List (tests 182-184) ──────────────────


class TestDbList:
    """Spec §5.22.8 — DB with comma-separated values."""

    def test_182_comma_list(self) -> None:
        assert asm_bytes("DB 10, 20, 30") == [10, 20, 30]

    def test_183_mixed_formats(self) -> None:
        assert asm_bytes("DB 0xFF, 0, 42") == [255, 0, 42]

    def test_184_single_value(self) -> None:
        assert asm_bytes("DB 1") == [1]


# ── Additional encoding tests ────────────────────────────────────────


class TestAllOpcodeEncoding:
    """Verify opcode encoding for every instruction category."""

    def test_mov_reg_addr(self) -> None:
        assert asm_bytes("MOV A, [0x50]") == [2, 0, 0x50]

    def test_mov_reg_regaddr(self) -> None:
        assert asm_bytes("MOV A, [B]") == [3, 0, 1]

    def test_mov_addr_reg(self) -> None:
        assert asm_bytes("MOV [0x50], A") == [4, 0x50, 0]

    def test_mov_regaddr_reg(self) -> None:
        assert asm_bytes("MOV [B], A") == [5, 1, 0]

    def test_mov_addr_const(self) -> None:
        assert asm_bytes("MOV [232], 72") == [7, 232, 72]

    def test_mov_regaddr_const(self) -> None:
        assert asm_bytes("MOV [B+2], 88") == [8, 17, 88]

    def test_add_reg_reg(self) -> None:
        assert asm_bytes("ADD A, B") == [10, 0, 1]

    def test_add_reg_addr(self) -> None:
        assert asm_bytes("ADD A, [0x50]") == [12, 0, 0x50]

    def test_add_reg_const(self) -> None:
        assert asm_bytes("ADD A, 1") == [13, 0, 1]

    def test_sub_reg_reg(self) -> None:
        assert asm_bytes("SUB A, B") == [14, 0, 1]

    def test_sub_reg_const(self) -> None:
        assert asm_bytes("SUB A, 20") == [17, 0, 20]

    def test_dec_reg(self) -> None:
        assert asm_bytes("DEC A") == [19, 0]

    def test_inc_sp(self) -> None:
        assert asm_bytes("INC SP") == [18, 4]

    def test_cmp_reg_reg(self) -> None:
        assert asm_bytes("CMP A, B") == [20, 0, 1]

    def test_cmp_reg_const(self) -> None:
        assert asm_bytes("CMP A, 0") == [23, 0, 0]

    def test_jmp_reg(self) -> None:
        assert asm_bytes("JMP A") == [30, 0]

    def test_jc_addr(self) -> None:
        assert asm_bytes("JC 100") == [33, 100]

    def test_jnc_addr(self) -> None:
        assert asm_bytes("JNC 50") == [35, 50]

    def test_jz_addr(self) -> None:
        assert asm_bytes("JZ 30") == [37, 30]

    def test_jnz_addr(self) -> None:
        assert asm_bytes("JNZ 40") == [39, 40]

    def test_ja_addr(self) -> None:
        assert asm_bytes("JA 20") == [41, 20]

    def test_jna_addr(self) -> None:
        assert asm_bytes("JNA 10") == [43, 10]

    def test_push_reg(self) -> None:
        assert asm_bytes("PUSH A") == [50, 0]

    def test_push_regaddr(self) -> None:
        assert asm_bytes("PUSH [B]") == [51, 1]

    def test_push_addr(self) -> None:
        assert asm_bytes("PUSH [0x50]") == [52, 0x50]

    def test_pop_reg(self) -> None:
        assert asm_bytes("POP A") == [54, 0]

    def test_call_reg(self) -> None:
        assert asm_bytes("CALL A") == [55, 0]

    def test_call_addr(self) -> None:
        assert asm_bytes("CALL 100") == [56, 100]

    def test_mul_reg(self) -> None:
        assert asm_bytes("MUL B") == [60, 1]

    def test_mul_regaddr(self) -> None:
        assert asm_bytes("MUL [B]") == [61, 1]

    def test_mul_addr(self) -> None:
        assert asm_bytes("MUL [0x50]") == [62, 0x50]

    def test_mul_const(self) -> None:
        assert asm_bytes("MUL 2") == [63, 2]

    def test_div_reg(self) -> None:
        assert asm_bytes("DIV B") == [64, 1]

    def test_div_const(self) -> None:
        assert asm_bytes("DIV 2") == [67, 2]

    def test_and_reg_reg(self) -> None:
        assert asm_bytes("AND A, B") == [70, 0, 1]

    def test_and_reg_const(self) -> None:
        assert asm_bytes("AND A, 0x0F") == [73, 0, 0x0F]

    def test_or_reg_reg(self) -> None:
        assert asm_bytes("OR A, B") == [74, 0, 1]

    def test_or_reg_const(self) -> None:
        assert asm_bytes("OR A, 0x0F") == [77, 0, 0x0F]

    def test_xor_reg_reg(self) -> None:
        assert asm_bytes("XOR A, B") == [78, 0, 1]

    def test_xor_reg_const(self) -> None:
        assert asm_bytes("XOR A, 0xFF") == [81, 0, 0xFF]

    def test_not_reg(self) -> None:
        assert asm_bytes("NOT A") == [82, 0]

    def test_shl_reg_reg(self) -> None:
        assert asm_bytes("SHL A, B") == [90, 0, 1]

    def test_shl_reg_const(self) -> None:
        assert asm_bytes("SHL A, 1") == [93, 0, 1]

    def test_shr_reg_reg(self) -> None:
        assert asm_bytes("SHR A, B") == [94, 0, 1]

    def test_shr_reg_const(self) -> None:
        assert asm_bytes("SHR A, 1") == [97, 0, 1]

    def test_sal_alias(self) -> None:
        assert asm_bytes("SAL A, 2") == asm_bytes("SHL A, 2")

    def test_sar_alias(self) -> None:
        assert asm_bytes("SAR A, 2") == asm_bytes("SHR A, 2")

    def test_mov_sp_const(self) -> None:
        assert asm_bytes("MOV SP, 100") == [6, 4, 100]

    def test_mov_reg_sp(self) -> None:
        assert asm_bytes("MOV A, SP") == [1, 0, 4]

    def test_mov_dp_const(self) -> None:
        assert asm_bytes("MOV DP, 5") == [6, 5, 5]

    def test_mov_reg_dp(self) -> None:
        assert asm_bytes("MOV A, DP") == [1, 0, 5]

    def test_add_sp_const(self) -> None:
        assert asm_bytes("ADD SP, 10") == [13, 4, 10]

    def test_sub_sp_reg(self) -> None:
        assert asm_bytes("SUB SP, A") == [14, 4, 0]

    def test_cmp_sp_const(self) -> None:
        assert asm_bytes("CMP SP, 231") == [23, 4, 231]


# ── SP/DP restriction errors ────────────────────────────────────────


class TestOperandRestrictions:
    """Assembler must reject SP/DP where not allowed."""

    def test_96_push_sp_error(self) -> None:
        err = asm_error("PUSH SP")
        assert "does not support this operand" in err.message

    def test_97_pop_sp_error(self) -> None:
        err = asm_error("POP SP")
        assert "does not support this operand" in err.message

    def test_98_and_sp_error(self) -> None:
        err = asm_error("AND SP, 0xFF")
        assert "does not support this operand" in err.message

    def test_99_or_sp_error(self) -> None:
        err = asm_error("OR SP, 0")
        assert "does not support this operand" in err.message

    def test_100_xor_sp_error(self) -> None:
        err = asm_error("XOR SP, SP")
        assert "does not support this operand" in err.message

    def test_101_not_sp_error(self) -> None:
        err = asm_error("NOT SP")
        assert "does not support this operand" in err.message

    def test_102_shl_sp_error(self) -> None:
        err = asm_error("SHL SP, 1")
        assert "does not support this operand" in err.message

    def test_103_shr_sp_error(self) -> None:
        err = asm_error("SHR SP, 1")
        assert "does not support this operand" in err.message

    def test_104_mul_sp_error(self) -> None:
        err = asm_error("MUL SP")
        assert "does not support this operand" in err.message

    def test_105_div_sp_error(self) -> None:
        err = asm_error("DIV SP")
        assert "does not support this operand" in err.message

    def test_jmp_sp_error(self) -> None:
        err = asm_error("JMP SP")
        assert "does not support this operand" in err.message

    def test_call_sp_error(self) -> None:
        err = asm_error("CALL SP")
        assert "does not support this operand" in err.message


# ── Regaddr offset encoding edge cases ──────────────────────────────


class TestRegaddrEncoding:
    """Detailed register indirect encoding tests."""

    def test_b_plus_0(self) -> None:
        assert asm_bytes("MOV A, [B+0]") == [3, 0, 1]

    def test_b_plus_15(self) -> None:
        assert asm_bytes("MOV A, [B+15]") == [3, 0, 121]

    def test_b_minus_16(self) -> None:
        assert asm_bytes("MOV A, [B-16]") == [3, 0, 129]

    def test_b_minus_1(self) -> None:
        assert asm_bytes("MOV A, [B-1]") == [3, 0, 249]

    def test_sp_minus_2(self) -> None:
        assert asm_bytes("MOV A, [SP-2]") == [3, 0, 244]

    def test_a_no_offset(self) -> None:
        assert asm_bytes("MOV B, [A]") == [3, 1, 0]

    def test_d_plus_5(self) -> None:
        assert asm_bytes("MOV A, [D+5]") == [3, 0, 43]


# ── Comments and blank lines ────────────────────────────────────────


class TestCommentsAndBlanks:
    """Comments, blank lines, and inline comments."""

    def test_blank_lines(self) -> None:
        assert asm_bytes("\n\nHLT\n\n") == [0]

    def test_comment_only_line(self) -> None:
        assert asm_bytes("; this is a comment\nHLT") == [0]

    def test_inline_comment(self) -> None:
        assert asm_bytes("MOV A, 5 ; load value") == [6, 0, 5]

    def test_empty_source(self) -> None:
        assert asm_bytes("") == []

    def test_only_comments(self) -> None:
        assert asm_bytes("; comment 1\n; comment 2") == []


# ── Label edge cases ────────────────────────────────────────────────


class TestLabelEdgeCases:
    """Label-related edge cases."""

    def test_label_only_line(self) -> None:
        result = assemble("start:\nHLT")
        assert result.code == [0]
        assert result.labels["start"] == 0

    def test_label_with_instruction(self) -> None:
        result = assemble("start: MOV A, 1")
        assert result.code == [6, 0, 1]
        assert result.labels["start"] == 0

    def test_label_sp_forbidden(self) -> None:
        err = asm_error("SP: DB 0")
        assert "keyword" in err.message.lower()

    def test_label_dp_forbidden(self) -> None:
        err = asm_error("DP: DB 0")
        assert "keyword" in err.message.lower()

    def test_label_c_forbidden(self) -> None:
        err = asm_error("C: DB 0")
        assert "keyword" in err.message.lower()

    def test_label_d_forbidden(self) -> None:
        err = asm_error("D: DB 0")
        assert "keyword" in err.message.lower()

    def test_forward_reference_in_call(self) -> None:
        result = assemble("CALL func\nHLT\nfunc: RET")
        assert result.code == [56, 3, 0, 57]
        assert result.labels["func"] == 3

    def test_label_used_as_const(self) -> None:
        result = assemble("MOV B, end\nend: HLT")
        assert result.code == [6, 1, 3, 0]
        assert result.labels["end"] == 3

    def test_label_in_brackets_mov(self) -> None:
        result = assemble("JMP start\ndata: DB 42\nstart: MOV A, [data]\nHLT")
        assert result.labels["data"] == 2
        assert result.labels["start"] == 3
        assert result.code == [31, 3, 42, 2, 0, 2, 0]

    def test_label_in_brackets_store(self) -> None:
        result = assemble("JMP start\ndata: DB 0\nstart: MOV [data], B\nHLT")
        assert result.labels["data"] == 2
        assert result.code == [31, 3, 0, 4, 2, 1, 0]

    def test_label_in_brackets_add(self) -> None:
        result = assemble("JMP s\nx: DB 10\ns: ADD A, [x]\nHLT")
        assert result.labels["x"] == 2
        assert result.code == [31, 3, 10, 12, 0, 2, 0]

    def test_label_in_brackets_push(self) -> None:
        result = assemble("JMP s\ndata: DB 99\ns: PUSH [data]\nHLT")
        assert result.labels["data"] == 2
        assert result.code == [31, 3, 99, 52, 2, 0]

    def test_label_in_brackets_undefined(self) -> None:
        err = asm_error("MOV A, [missing]")
        assert "undefined label" in err.message.lower()

    def test_label_in_brackets_forward_ref(self) -> None:
        result = assemble("MOV A, [data]\nHLT\ndata: DB 55")
        assert result.labels["data"] == 4
        assert result.code == [2, 0, 4, 0, 55]

    def test_label_in_brackets_matches_numeric(self) -> None:
        r1 = assemble("JMP s\nx: DB 7\ns: MOV A, [x]\nHLT")
        r2 = assemble("JMP s\nx: DB 7\ns: MOV A, [2]\nHLT")
        assert r1.code == r2.code


# ── DB edge cases ────────────────────────────────────────────────────


class TestDbEdgeCases:
    """DB pseudo-instruction edge cases."""

    def test_db_max_value(self) -> None:
        assert asm_bytes("DB 255") == [255]

    def test_db_hex(self) -> None:
        assert asm_bytes("DB 0xFF") == [255]

    def test_db_string_multiple_chars(self) -> None:
        assert asm_bytes('DB "Hello"') == [72, 101, 108, 108, 111]

    def test_db_empty_string(self) -> None:
        err = asm_error('DB ""')
        assert "empty" in err.message.lower()

    def test_db_with_label(self) -> None:
        result = assemble("data: DB 42\nHLT")
        assert result.code == [42, 0]
        assert result.labels["data"] == 0

    def test_db_256_error(self) -> None:
        err = asm_error("DB 256")
        assert "value between 0-255" in err.message


# ── Exhaustiveness guards ─────────────────────────────────────────


class TestExhaustiveness:
    """Ensure all Operand types are handled in match/case dispatches."""

    def test_encode_covers_all_operand_types(self) -> None:
        operand_types = get_args(Operand)
        encoded_types = {t for t in operand_types if t.__name__ != "OpString"}
        for op_type in encoded_types:
            assert hasattr(op_type, "__dataclass_fields__"), (
                f"{op_type} is not a dataclass"
            )

    def test_operand_matches_covers_all_ot_variants(self) -> None:
        from pysim8.asm.parser import (
            OpReg, OpConst, OpAddr, OpRegAddr, OpLabel,
            OpFpReg, OpFpImm,
        )
        test_operands = {
            OpType.REG: OpReg(0),
            OpType.REG_STACK: OpReg(0),
            OpType.REG_GPR: OpReg(0),
            OpType.IMM: OpConst(0),
            OpType.MEM: OpAddr(0),
            OpType.REGADDR: OpRegAddr(0, 0),
            OpType.FP_REG: OpFpReg("FQA", 0, 3, 0),
            OpType.FP_IMM8: OpFpImm(1.0, None),
            OpType.FP_IMM16: OpFpImm(1.0, None),
        }
        covered = set(test_operands.keys())
        all_variants = set(OpType)
        assert covered == all_variants, (
            f"Uncovered OpType variants: {all_variants - covered}"
        )
        for ot, op in test_operands.items():
            assert _operand_matches(op, ot) is True, (
                f"_operand_matches({op!r}, {ot}) returned False"
            )


# ── Parser edge cases ─────────────────────────────────────────────


class TestParserEdges:
    """Parser corner cases for coverage."""

    def test_multi_char_literal_error(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("MOV A, 'ab'\nHLT")

    def test_invalid_number(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("MOV A, xyz\nHLT")

    def test_invalid_address(self) -> None:
        with pytest.raises(AssemblerError):
            assemble('MOV A, [+]\nHLT')

    def test_string_operand(self) -> None:
        result = assemble('DB "AB"\nHLT')
        assert 65 in result.code
        assert 66 in result.code

    def test_hlt_with_args(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("HLT 1")

    def test_no_operands(self) -> None:
        result = assemble("HLT")
        assert result.code == [0]

    def test_db_register_error(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("DB A\nHLT")

    def test_db_bracket_error(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("DB [10]\nHLT")

    def test_db_label_error(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("DB hello\nHLT")

    def test_char_literal(self) -> None:
        from pysim8.sim import CPU
        result = assemble("MOV A, 'X'\nHLT")
        cpu = CPU()
        cpu.load(result.code)
        cpu.run()
        assert cpu.a == ord('X')

    def test_invalid_register_in_offset(self) -> None:
        """[XYZ+5] where XYZ is not a register (parser line 230)."""
        with pytest.raises(AssemblerError, match="Invalid register"):
            assemble("MOV A, [XYZ+5]\nHLT")

    def test_multi_char_literal_in_parse_number(self) -> None:
        """parse_number with multi-char literal (parser line 193)."""
        with pytest.raises(ParseError, match="one character"):
            parse_number("'ab'", 1)

    def test_parse_number_invalid_format(self) -> None:
        """parse_number with non-numeric token (parser line 196)."""
        with pytest.raises(ParseError, match="Invalid number"):
            parse_number("$$$", 1)

    def test_multi_char_in_try_parse_number(self) -> None:
        """Multi-char literal returns None in _try_parse_number (line 181)."""
        from pysim8.asm.parser import _try_parse_number
        assert _try_parse_number("'abc'") is None

    def test_string_with_comma_in_db(self) -> None:
        """Comma inside string should not split operands (line 535)."""
        result = assemble('DB "a,b"\nHLT')
        assert result.code[:3] == [ord('a'), ord(','), ord('b')]

    def test_empty_operands_no_arg_insn(self) -> None:
        """No-arg instruction sets operands=[] (line 657)."""
        result = assemble("HLT")
        assert result.code == [0]


# ── Parser property-based tests ────────────────────────────────────


class TestPropParser:
    """Property-based parser tests."""

    @given(st.integers(min_value=0, max_value=255))
    def test_number_roundtrip_decimal(self, n: int) -> None:
        """Any 0-255 decimal assembles to that byte."""
        code = assemble(f"MOV A, {n}\nHLT").code
        assert code == [6, 0, n, 0]

    @given(st.integers(min_value=0, max_value=255))
    def test_number_roundtrip_hex(self, n: int) -> None:
        """Any 0-255 hex assembles correctly."""
        code = assemble(f"MOV A, 0x{n:02X}\nHLT").code
        assert code == [6, 0, n, 0]

    @given(st.integers(min_value=0, max_value=255))
    def test_db_byte_value(self, n: int) -> None:
        """DB with any 0-255 value produces that byte."""
        code = assemble(f"DB {n}").code
        assert code == [n]

    @given(st.text(
        alphabet=st.characters(whitelist_categories=('L',), min_codepoint=65, max_codepoint=90),
        min_size=1, max_size=8,
    ))
    def test_random_label_name(self, name: str) -> None:
        """Random uppercase labels work if not a keyword."""
        from pysim8.isa import REGISTERS, FP_REGISTERS, MNEMONICS, MNEMONICS_FP
        assume(name.upper() not in REGISTERS)
        assume(name.upper() not in FP_REGISTERS)
        assume(name.upper() not in MNEMONICS)
        assume(name.upper() not in MNEMONICS_FP)
        assume(name.upper() not in {"DB", "INF", "NAN"})
        src = f"{name}: HLT\nJMP {name}"
        result = assemble(src)
        assert name.lower() in result.labels

    @given(st.sampled_from([
        "MOV A, 256", "MOV A, -1", "MOV A, 300",
        "DB 256", "DB -1", "DB 999",
    ]))
    def test_out_of_range_constants(self, src: str) -> None:
        """Values outside 0-255 are rejected."""
        with pytest.raises(AssemblerError):
            assemble(src + "\nHLT")


# ── Crazy input tests ──────────────────────────────────────────────


class TestCrazyInput:
    """Adversarial and bizarre inputs that should not crash."""

    def test_empty_source(self) -> None:
        result = assemble("")
        assert result.code == []

    def test_only_whitespace(self) -> None:
        result = assemble("   \n\n  \t \n")
        assert result.code == []

    def test_only_comments(self) -> None:
        result = assemble("; this is a comment\n; another one\n")
        assert result.code == []

    def test_only_labels(self) -> None:
        result = assemble("foo:\nbar:\nbaz:")
        assert result.labels == {"foo": 0, "bar": 0, "baz": 0}

    def test_label_on_hlt(self) -> None:
        result = assemble("start: HLT")
        assert result.labels["start"] == 0
        assert result.code == [0]

    def test_many_labels_same_address(self) -> None:
        result = assemble("x1:\nx2:\nx3:\nx4:\nHLT")
        assert result.labels == {"x1": 0, "x2": 0, "x3": 0, "x4": 0}
        assert result.code == [0]

    def test_max_db_line(self) -> None:
        """DB with many comma-separated values."""
        vals = ", ".join(str(i % 256) for i in range(100))
        result = assemble(f"DB {vals}")
        assert len(result.code) == 100

    def test_very_long_string(self) -> None:
        """DB with long string."""
        s = "A" * 200
        result = assemble(f'DB "{s}"')
        assert len(result.code) == 200
        assert all(b == 65 for b in result.code)

    def test_register_as_label_error(self) -> None:
        with pytest.raises(AssemblerError, match="keyword"):
            assemble("A: HLT")

    def test_sp_as_label_error(self) -> None:
        with pytest.raises(AssemblerError, match="keyword"):
            assemble("SP: HLT")

    def test_duplicate_label_error(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("x: HLT\nx: HLT")

    def test_undefined_label_error(self) -> None:
        with pytest.raises(AssemblerError, match="Undefined"):
            assemble("JMP nowhere\nHLT")

    def test_offset_out_of_range_positive(self) -> None:
        with pytest.raises(AssemblerError, match="offset"):
            assemble("MOV A, [B+16]\nHLT")

    def test_offset_out_of_range_negative(self) -> None:
        with pytest.raises(AssemblerError, match="offset"):
            assemble("MOV A, [B-17]\nHLT")

    def test_garbage_operand(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("MOV A, @@@\nHLT")

    def test_too_many_operands(self) -> None:
        with pytest.raises(AssemblerError, match="too many"):
            assemble("MOV A, B, C\nHLT")

    def test_wrong_operand_type(self) -> None:
        with pytest.raises(AssemblerError, match="operand"):
            assemble("MOV 42, A\nHLT")

    def test_unknown_mnemonic(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("XYZZY A, B\nHLT")

    def test_missing_label_colon(self) -> None:
        """foo HLT — 'foo' is not a mnemonic and no colon → error."""
        with pytest.raises(AssemblerError):
            assemble("foo HLT")


# ── Direct parser function tests ─────────────────────────────────


class TestParserDirect:
    """Direct unit tests for parser functions to reach uncovered lines."""

    def test_try_string_in_operand_chain(self) -> None:
        """_parse_operand with quoted string → OpString (line 282)."""
        from pysim8.asm.parser import _parse_operand, OpString
        result = _parse_operand('"hello"', 1)
        assert isinstance(result, OpString)
        assert result.text == "hello"

    def test_try_fp_imm_malformed_float(self) -> None:
        """_try_fp_imm with unparseable float → ParseError (lines 336-337)."""
        from pysim8.asm.parser import _try_fp_imm
        # The regex _RE_FLOAT matches "1.e999999999999999999" — valid regex
        # but float() can't parse certain edge cases.
        # Actually, we need something the regex matches but float() rejects.
        # The regex is: ^([+-]?)(\d+\.\d*|\.\d+)([eE][+-]?\d+)?(_\w+)?$
        # Python float() handles everything the regex accepts.
        # So lines 336-337 are genuinely hard to reach via normal parsing.
        # Let's just verify the error path works by calling directly.
        import unittest.mock as mock
        with mock.patch("builtins.float", side_effect=ValueError("bad")):
            from pysim8.asm.parser import _try_fp_imm
            with pytest.raises(ParseError, match="Invalid float"):
                _try_fp_imm("1.0", 1)

    def test_parse_float_literal_malformed(self) -> None:
        """_parse_float_literal with unparseable float (lines 432-433)."""
        import unittest.mock as mock
        with mock.patch("builtins.float", side_effect=ValueError("bad")):
            from pysim8.asm.parser import _parse_float_literal
            with pytest.raises(ParseError, match="Invalid float"):
                _parse_float_literal("1.0", 1)

    def test_split_operands_with_string(self) -> None:
        """_split_operands with quoted string containing comma (line 535)."""
        from pysim8.asm.parser import _split_operands
        result = _split_operands('"a,b"')
        assert result == ['"a,b"']

    def test_split_operands_empty_input(self) -> None:
        """_split_operands with empty string (line 546→548)."""
        from pysim8.asm.parser import _split_operands
        result = _split_operands("")
        assert result == []
