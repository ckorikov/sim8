"""FP assembler tests for arch=2.

Tests verify FP instruction encoding, DB float literals, and error
handling. All tests use arch=2 unless explicitly testing arch=1
regression.
"""

from __future__ import annotations

import struct

import pytest
from hypothesis import given
from hypothesis import strategies as st

from pysim8.asm import assemble, AssemblerError
from pysim8.asm.parser import OpFpImm, OpConst


def asm_bytes(source: str, arch: int = 2) -> list[int]:
    """Assemble and return machine code bytes."""
    return assemble(source, arch=arch).code


def asm_error(source: str, arch: int = 2) -> AssemblerError:
    """Assemble expecting an error; return the exception."""
    with pytest.raises(AssemblerError) as exc_info:
        assemble(source, arch=arch)
    return exc_info.value


class TestFpmEncoding:
    """FPM byte encoding formula: (phys << 6) | (pos << 3) | fmt."""

    def test_fa_fpm(self) -> None:
        """FA + .F -> pos=0, fmt=0 -> FPM=0x00."""
        code = asm_bytes("FABS.F FA\nHLT")
        assert code == [142, 0x00, 0]

    def test_fha_fpm(self) -> None:
        """FHA + .H -> pos=0, fmt=1 -> FPM=0x01."""
        code = asm_bytes("FABS.H FHA\nHLT")
        assert code == [142, 0x01, 0]

    def test_fhb_fpm(self) -> None:
        """FHB + .H -> pos=1, fmt=1 -> FPM=0x09."""
        code = asm_bytes("FABS.H FHB\nHLT")
        assert code == [142, 0x09, 0]

    def test_fqa_o3_fpm(self) -> None:
        """FQA + .O3 -> pos=0, fmt=3 -> FPM=0x03."""
        code = asm_bytes("FABS.O3 FQA\nHLT")
        assert code == [142, 0x03, 0]

    def test_fqd_o2_fpm(self) -> None:
        """FQD + .O2 -> pos=3, fmt=4 -> FPM=0x1C."""
        code = asm_bytes("FABS.O2 FQD\nHLT")
        assert code == [142, 0x1C, 0]

    def test_fhb_bf_fpm(self) -> None:
        """FHB + .BF -> pos=1, fmt=2 -> FPM=0x0A."""
        code = asm_bytes("FABS.BF FHB\nHLT")
        assert code == [142, 0x0A, 0]


class TestFmovEncoding:
    """FMOV load/store encoding."""

    def test_fmov_load_addr(self) -> None:
        """FMOV.F FA, [0x50] -> [128, 0x00, 0x50]."""
        code = asm_bytes("FMOV.F FA, [0x50]\nHLT")
        assert code == [128, 0x00, 0x50, 0]

    def test_fmov_load_regaddr(self) -> None:
        """FMOV.H FHA, [B] -> [129, 0x01, regaddr(B)]."""
        code = asm_bytes("FMOV.H FHA, [B]\nHLT")
        assert code == [129, 0x01, 0x01, 0]

    def test_fmov_store_addr(self) -> None:
        """FMOV.F [0x50], FA -> [130, 0x00, 0x50]."""
        code = asm_bytes("FMOV.F [0x50], FA\nHLT")
        assert code == [130, 0x00, 0x50, 0]

    def test_fmov_store_regaddr(self) -> None:
        """FMOV.H [B], FHA -> [131, 0x01, 0x01]."""
        code = asm_bytes("FMOV.H [B], FHA\nHLT")
        assert code == [131, 0x01, 0x01, 0]


class TestFaddEncoding:
    """FADD per-format encoding."""

    def test_fadd_f(self) -> None:
        code = asm_bytes("FADD.F FA, [0x50]\nHLT")
        assert code == [132, 0x00, 0x50, 0]

    def test_fadd_h(self) -> None:
        code = asm_bytes("FADD.H FHA, [0x50]\nHLT")
        assert code == [132, 0x01, 0x50, 0]

    def test_fadd_bf(self) -> None:
        code = asm_bytes("FADD.BF FHB, [0x50]\nHLT")
        assert code == [132, 0x0A, 0x50, 0]

    def test_fadd_o3(self) -> None:
        code = asm_bytes("FADD.O3 FQA, [0x50]\nHLT")
        assert code == [132, 0x03, 0x50, 0]

    def test_fadd_o2(self) -> None:
        code = asm_bytes("FADD.O2 FQB, [0x50]\nHLT")
        assert code == [132, 0x0C, 0x50, 0]


class TestUnaryEncoding:
    """FABS, FNEG, FSQRT unary instruction encoding."""

    def test_fabs(self) -> None:
        code = asm_bytes("FABS.F FA\nHLT")
        assert code == [142, 0x00, 0]

    def test_fneg(self) -> None:
        code = asm_bytes("FNEG.H FHB\nHLT")
        assert code == [143, 0x09, 0]

    def test_fsqrt(self) -> None:
        code = asm_bytes("FSQRT.BF FHA\nHLT")
        assert code == [144, 0x02, 0]


class TestControlEncoding:
    """FCLR, FSTAT, FCFG, FSCFG control instructions."""

    def test_fclr(self) -> None:
        code = asm_bytes("FCLR\nHLT")
        assert code == [152, 0]

    def test_fstat(self) -> None:
        code = asm_bytes("FSTAT A\nHLT")
        assert code == [149, 0, 0]

    def test_fcfg(self) -> None:
        code = asm_bytes("FCFG B\nHLT")
        assert code == [150, 1, 0]

    def test_fscfg(self) -> None:
        code = asm_bytes("FSCFG C\nHLT")
        assert code == [151, 2, 0]


class TestFcvtEncoding:
    """FCVT dual suffix encoding."""

    def test_fcvt_h_f(self) -> None:
        """FCVT.H.F FHA, FA -> [146, 0x01, 0x00]."""
        code = asm_bytes("FCVT.H.F FHA, FA\nHLT")
        assert code == [146, 0x01, 0x00, 0]

    def test_fcvt_f_h(self) -> None:
        """FCVT.F.H FA, FHA -> [146, 0x00, 0x01]."""
        code = asm_bytes("FCVT.F.H FA, FHA\nHLT")
        assert code == [146, 0x00, 0x01, 0]


class TestFitofFftoiEncoding:
    """FITOF and FFTOI encoding."""

    def test_fitof(self) -> None:
        """FITOF.F FA, A -> [147, 0x00, 0x00]."""
        code = asm_bytes("FITOF.F FA, A\nHLT")
        assert code == [147, 0x00, 0x00, 0]

    def test_fftoi(self) -> None:
        """FFTOI.F A, FA -> [148, 0x00, 0x00].

        Note: FPM before GPR in encoding.
        """
        code = asm_bytes("FFTOI.F A, FA\nHLT")
        assert code == [148, 0x00, 0x00, 0]


class TestRegRegEncoding:
    """Register-to-register FP operations."""

    def test_fadd_rr(self) -> None:
        """FADD.H FHA, FHB -> [153, 0x01, 0x09]."""
        code = asm_bytes("FADD.H FHA, FHB\nHLT")
        assert code == [153, 0x01, 0x09, 0]

    def test_fcmp_rr_self(self) -> None:
        """FCMP.F FA, FA -> [157, 0x00, 0x00]."""
        code = asm_bytes("FCMP.F FA, FA\nHLT")
        assert code == [157, 0x00, 0x00, 0]


class TestFclassEncoding:
    """FCLASS encoding."""

    def test_fclass(self) -> None:
        """FCLASS.F A, FA -> [158, 0x00, 0x00]."""
        code = asm_bytes("FCLASS.F A, FA\nHLT")
        assert code == [158, 0x00, 0x00, 0]


class TestFmaddEncoding:
    """FMADD 4-byte encoding."""

    def test_fmadd_addr(self) -> None:
        """FMADD.H FHA, FHB, [0x50] -> [159, 0x01, 0x09, 0x50]."""
        code = asm_bytes("FMADD.H FHA, FHB, [0x50]\nHLT")
        assert code == [159, 0x01, 0x09, 0x50, 0]

    def test_fmadd_regaddr(self) -> None:
        """FMADD.F FA, FA, [B] -> [160, 0x00, 0x00, 0x01]."""
        code = asm_bytes("FMADD.F FA, FA, [B]\nHLT")
        assert code == [160, 0x00, 0x00, 0x01, 0]


class TestDbFloatLiterals:
    """DB float literal encoding."""

    def test_db_float32_default(self) -> None:
        """DB 1.0 -> 4 bytes float32 LE."""
        code = asm_bytes("DB 1.0")
        assert code == list(struct.pack("<f", 1.0))

    def test_db_float32_explicit(self) -> None:
        """DB 1.0_f -> same as default."""
        code = asm_bytes("DB 1.0_f")
        assert code == list(struct.pack("<f", 1.0))

    def test_db_float16(self) -> None:
        """DB 1.0_h -> 2 bytes float16 LE."""
        code = asm_bytes("DB 1.0_h")
        assert code == list(struct.pack("<e", 1.0))

    def test_db_bfloat16(self) -> None:
        """DB 1.0_bf -> 2 bytes bfloat16 LE (top 2 bytes of float32)."""
        code = asm_bytes("DB 1.0_bf")
        f32 = struct.pack("<f", 1.0)
        assert code == list(f32[2:])

    def test_db_inf(self) -> None:
        """DB inf -> float32 +Infinity."""
        code = asm_bytes("DB inf")
        assert code == list(struct.pack("<f", float("inf")))

    def test_db_nan(self) -> None:
        """DB nan_h -> float16 NaN, 2 bytes."""
        code = asm_bytes("DB nan_h")
        assert len(code) == 2
        raw = int.from_bytes(bytes(code), "little")
        assert (raw & 0x7C00) == 0x7C00  # exponent all ones
        assert (raw & 0x03FF) != 0       # non-zero payload

    def test_db_float_array(self) -> None:
        """DB 1.0, 2.0 -> 8 bytes (two float32)."""
        code = asm_bytes("DB 1.0, 2.0")
        expected = list(struct.pack("<f", 1.0)) + list(
            struct.pack("<f", 2.0)
        )
        assert code == expected

    def test_db_negative_float(self) -> None:
        """DB -1.5 -> float32 of -1.5."""
        code = asm_bytes("DB -1.5")
        assert code == list(struct.pack("<f", -1.5))


class TestExmySuffix:
    """EXMY suffix aliases."""

    def test_e8m23(self) -> None:
        code = asm_bytes("FABS.E8M23 FA\nHLT")
        assert code == [142, 0x00, 0]

    def test_e5m10(self) -> None:
        code = asm_bytes("FABS.E5M10 FHA\nHLT")
        assert code == [142, 0x01, 0]


class TestFpErrors:
    """FP assembler error handling."""

    def test_arch1_rejects_fp(self) -> None:
        """arch=1 does not recognize FP mnemonics."""
        e = asm_error("FADD.F FA, [0x50]\nHLT", arch=1)
        assert (
            "Invalid instruction" in e.message
            or "Syntax error" in e.message
        )

    def test_missing_suffix(self) -> None:
        """FP data instruction without suffix -> error."""
        e = asm_error("FADD FA, [0x50]\nHLT")
        assert "suffix" in e.message.lower()

    def test_width_mismatch(self) -> None:
        """Suffix width doesn't match register width."""
        e = asm_error("FADD.F FHA, [0x50]\nHLT")
        assert (
            "match" in e.message.lower()
            or "width" in e.message.lower()
        )

    def test_unknown_suffix(self) -> None:
        """Unknown format suffix."""
        e = asm_error("FADD.X FA, [0x50]\nHLT")
        assert (
            "suffix" in e.message.lower()
            or "Invalid" in e.message
        )

    def test_fp_reg_as_label_forbidden(self) -> None:
        """FP register name as label is forbidden."""
        e = asm_error("FA: HLT")
        assert "keyword" in e.message.lower()

    def test_db_float_int_mix(self) -> None:
        """Cannot mix float and int in DB."""
        e = asm_error("DB 1.0, 42")
        assert "mix" in e.message.lower()

    def test_case_insensitive_suffix(self) -> None:
        """Suffixes are case-insensitive."""
        code = asm_bytes("FABS.f FA\nHLT")
        assert code == [142, 0x00, 0]

    def test_case_insensitive_fp_reg(self) -> None:
        """FP registers are case-insensitive."""
        code = asm_bytes("FABS.F fa\nHLT")
        assert code == [142, 0x00, 0]


class TestLabelWithFpInstructions:
    """Labels work with FP instructions."""

    def test_fp_and_label_coexist(self) -> None:
        """FP instructions and labels in the same program."""
        code = asm_bytes(
            "FABS.F FA\nJMP end\nend: HLT"
        )
        # FABS.F FA -> [142, 0x00]
        # JMP end -> [31, 4]
        # end: HLT -> [0]
        assert code == [142, 0x00, 31, 4, 0]

    def test_label_before_fp_instruction(self) -> None:
        """Label on an FP instruction line."""
        result = assemble(
            "start: FABS.F FA\nHLT", arch=2
        )
        assert result.code == [142, 0x00, 0]
        assert result.labels["start"] == 0


class TestRegressionArch1:
    """Ensure arch=1 assembler still works identically."""

    def test_hlt(self) -> None:
        assert asm_bytes("HLT", arch=1) == [0]

    def test_mov_reg_const(self) -> None:
        assert asm_bytes("MOV A, 42\nHLT", arch=1) == [
            6, 0, 42, 0,
        ]

    def test_add(self) -> None:
        assert asm_bytes("ADD A, B\nHLT", arch=1) == [
            10, 0, 1, 0,
        ]


# ── Label in brackets with FP instructions ──────────────────────────


class TestFpLabelInBrackets:
    """[label] syntax with FP instructions."""

    def test_fmov_load_label(self) -> None:
        """FMOV.F FA, [data] → same as FMOV.F FA, [addr]."""
        src = "JMP s\ndata: DB 0, 0, 0, 0\ns: FMOV.F FA, [data]\nHLT"
        result = assemble(src, arch=2)
        assert result.labels["data"] == 2
        # FMOV.F FA, [2] → [128, 0x00, 2]
        assert result.code[6:9] == [128, 0x00, 2]

    def test_fadd_label(self) -> None:
        """FADD.F FA, [x] with label."""
        src = "JMP s\nx: DB 0, 0, 0, 0\ns: FADD.F FA, [x]\nHLT"
        result = assemble(src, arch=2)
        assert result.labels["x"] == 2
        # FADD.F FA, [2] → [132, 0x00, 2]
        assert result.code[6:9] == [132, 0x00, 2]


# ── FMOV immediate encoding ─────────────────────────────────────


class TestFmovImmEncoding:
    """FMOV with FP immediate encoding (opcodes 161-162)."""

    def test_fmov_imm_o3(self) -> None:
        """FMOV.O3 FQA, 1.5 -> [161, 0x03, 0x3C]."""
        code = asm_bytes("FMOV.O3 FQA, 1.5\nHLT")
        assert code == [161, 0x03, 0x3C, 0]

    def test_fmov_imm_o2(self) -> None:
        """FMOV.O2 FQB, 1.0 -> [161, 0x0C, 0x3C]."""
        code = asm_bytes("FMOV.O2 FQB, 1.0\nHLT")
        assert code == [161, 0x0C, 0x3C, 0]

    def test_fmov_imm_h(self) -> None:
        """FMOV.H FHA, 1.5 -> [162, 0x01, 0x00, 0x3E]."""
        code = asm_bytes("FMOV.H FHA, 1.5\nHLT")
        assert code == [162, 0x01, 0x00, 0x3E, 0]

    def test_fmov_imm_bf(self) -> None:
        """FMOV.BF FHB, 1.0 -> [162, 0x0A, 0x80, 0x3F]."""
        code = asm_bytes("FMOV.BF FHB, 1.0\nHLT")
        assert code == [162, 0x0A, 0x80, 0x3F, 0]

    def test_fmov_imm_explicit_suffix_match(self) -> None:
        """Explicit suffix on literal matching instruction suffix."""
        code = asm_bytes("FMOV.O3 FQA, 1.5_o3\nHLT")
        assert code == [161, 0x03, 0x3C, 0]

    def test_fmov_imm_no_suffix_h(self) -> None:
        """No suffix on literal, format from instruction suffix."""
        code = asm_bytes("FMOV.H FHA, 1.5\nHLT")
        assert code == [162, 0x01, 0x00, 0x3E, 0]

    def test_fmov_imm_suffix_mismatch_error(self) -> None:
        """Literal suffix mismatches instruction suffix."""
        e = asm_error("FMOV.O3 FQA, 1.5_h\nHLT")
        assert "mismatch" in e.message.lower()

    def test_fmov_imm_f32_error(self) -> None:
        """Float32 immediate not supported."""
        e = asm_error("FMOV.F FA, 1.5\nHLT")
        assert "float32" in e.message.lower() or "not supported" in e.message.lower()

    def test_fmov_imm_special_inf(self) -> None:
        """FMOV.H FHA, inf."""
        code = asm_bytes("FMOV.H FHA, inf\nHLT")
        assert code == [162, 0x01, 0x00, 0x7C, 0]

    def test_fmov_imm_special_nan(self) -> None:
        """FMOV.O2 FQA, nan."""
        code = asm_bytes("FMOV.O2 FQA, nan\nHLT")
        assert code == [161, 0x04, 0x7D, 0]

    def test_fmov_imm_negative(self) -> None:
        """FMOV.H FHA, -1.5."""
        code = asm_bytes("FMOV.H FHA, -1.5\nHLT")
        assert code == [162, 0x01, 0x00, 0xBE, 0]
        # float16 -1.5: sign=1 → high byte has bit 7 set
        assert code[3] & 0x80 == 0x80


class TestFbRegisterEncoding:
    """Assembler encoding tests for FB register (phys=1)."""

    def test_fb_float32_fpm(self) -> None:
        """FB = phys=1, pos=0, fmt=0 -> FPM = (1<<6)|0|0 = 0x40."""
        code = asm_bytes("FMOV.F FB, [100]\nHLT")
        assert code == [128, 0x40, 100, 0]

    def test_fhc_float16_fpm(self) -> None:
        """FHC = phys=1, pos=0, fmt=1 -> FPM = 0x41."""
        code = asm_bytes("FMOV.H FHC, [100]\nHLT")
        assert code == [128, 0x41, 100, 0]

    def test_fhd_bfloat16_fpm(self) -> None:
        """FHD = phys=1, pos=1, fmt=2 -> FPM = 0x4A."""
        code = asm_bytes("FMOV.BF FHD, [100]\nHLT")
        assert code == [128, 0x4A, 100, 0]

    def test_fqe_o3_fpm(self) -> None:
        """FQE = phys=1, pos=0, fmt=3 -> FPM = 0x43."""
        code = asm_bytes("FMOV.O3 FQE, [100]\nHLT")
        assert code == [128, 0x43, 100, 0]

    def test_fqh_o3_fpm(self) -> None:
        """FQH = phys=1, pos=3, fmt=3 -> FPM = 0x5B."""
        code = asm_bytes("FMOV.O3 FQH, [100]\nHLT")
        assert code == [128, 0x5B, 100, 0]

    def test_fadd_rr_cross_phys(self) -> None:
        """FADD_RR FQA, FQE: phys=0+phys=1 registers."""
        code = asm_bytes("FADD.O3 FQA, FQE\nHLT")
        # FADD_RR = 153, dst_fpm=0x03 (FQA), src_fpm=0x43 (FQE)
        assert code == [153, 0x03, 0x43, 0]

    def test_fmov_imm_fb(self) -> None:
        """FMOV.O3 FQE, 1.5 -> [161, 0x43, 0x3C]."""
        code = asm_bytes("FMOV.O3 FQE, 1.5\nHLT")
        assert code == [161, 0x43, 0x3C, 0]

    def test_fmov_imm_h_fb(self) -> None:
        """FMOV.H FHC, 1.5 -> [162, 0x41, 0x00, 0x3E]."""
        code = asm_bytes("FMOV.H FHC, 1.5\nHLT")
        assert code == [162, 0x41, 0x00, 0x3E, 0]

    def test_fcvt_fa_to_fb(self) -> None:
        """FCVT.O3.H FQE, FHA -> [146, 0x43, 0x01]."""
        code = asm_bytes("FCVT.O3.H FQE, FHA\nHLT")
        assert code == [146, 0x43, 0x01, 0]

    def test_fb_label_not_keyword(self) -> None:
        """FB is a keyword, cannot be used as label."""
        e = asm_error("FB: HLT")
        assert "keyword" in e.message.lower()


# ── FP parser edge cases ──────────────────────────────────────────


class TestFpParserEdges:
    """FP-specific parser coverage tests."""

    def test_fp_suffix_invalid(self) -> None:
        e = asm_error("FMOV.H FHA, 1.0_zz\nHLT")
        assert "invalid" in e.message.lower() or "suffix" in e.message.lower()

    def test_fp_control_with_suffix_error(self) -> None:
        e = asm_error("FSTAT.H A\nHLT")
        assert (
            "suffix" in e.message.lower()
            or "invalid" in e.message.lower()
            or "syntax" in e.message.lower()
        )

    def test_fcvt_missing_suffix(self) -> None:
        e = asm_error("FCVT.H FHA, FHB\nHLT")
        assert "suffix" in e.message.lower()

    def test_fp_mnemonic_missing_suffix(self) -> None:
        e = asm_error("FADD FHA, [100]\nHLT")
        assert "suffix" in e.message.lower()

    def test_db_mixed_float_int_error(self) -> None:
        e = asm_error("DB 1.0_h, 42\nHLT")
        assert "mix" in e.message.lower()

    def test_parse_float_special_neg_nan(self) -> None:
        result = assemble("DB -nan_h\nHLT", arch=2)
        assert result.code == [0x00, 0xFE, 0x00]

    def test_parse_float_with_exponent(self) -> None:
        result = assemble("DB 1.5e2_h\nHLT", arch=2)
        assert result.code == list(struct.pack("<e", 150.0)) + [0]


# ── FP codegen edge cases ─────────────────────────────────────────


class TestFpCodegenEdges:
    """FP-specific codegen coverage tests."""

    def test_db_float_valid(self) -> None:
        result = assemble("DB 1.0_h\nHLT", arch=2)
        assert result.code == list(struct.pack("<e", 1.0)) + [0]

    def test_fcvt_encoding(self) -> None:
        result = assemble("FCVT.H.F FHA, FA\nHLT", arch=2)
        assert result.code == [146, 0x01, 0x00, 0]

    def test_fcvt_non_fpreg_error(self) -> None:
        e = asm_error("FCVT.H.F A, B\nHLT", arch=2)
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "does not support" in e.message.lower()
        )

    def test_fmov_imm_4bit_error(self) -> None:
        e = asm_error("FMOV.N1 FOA, 1.0\nHLT", arch=2)
        assert (
            "not supported" in e.message.lower()
            or "invalid" in e.message.lower()
            or "syntax" in e.message.lower()
        )

    def test_fmov_imm_suffix_mismatch(self) -> None:
        e = asm_error("FMOV.H FHA, 1.0_bf\nHLT", arch=2)
        assert "mismatch" in e.message.lower()

    def test_undefined_label(self) -> None:
        e = asm_error("JMP nowhere\nHLT")
        assert "undefined label" in e.message.lower()


# ── ISA edge cases ────────────────────────────────────────────────


# ── FMOV reg-reg (opcode 145) ────────────────────────────────────


class TestFmovRrEncoding:
    """FMOV register-to-register encoding (opcode 145)."""

    def test_fmov_rr_h(self) -> None:
        """FMOV.H FHA, FHB -> [145, 0x01, 0x09]."""
        code = asm_bytes("FMOV.H FHA, FHB\nHLT")
        assert code == [145, 0x01, 0x09, 0]

    def test_fmov_rr_f(self) -> None:
        """FMOV.F FA, FB -> [145, 0x00, 0x40]."""
        code = asm_bytes("FMOV.F FA, FB\nHLT")
        assert code == [145, 0x00, 0x40, 0]

    def test_fmov_rr_o3(self) -> None:
        """FMOV.O3 FQA, FQB -> [145, 0x03, 0x0B]."""
        code = asm_bytes("FMOV.O3 FQA, FQB\nHLT")
        assert code == [145, 0x03, 0x0B, 0]

    def test_fmov_rr_cross_phys(self) -> None:
        """FMOV.H FHA, FHC -> [145, 0x01, 0x41]."""
        code = asm_bytes("FMOV.H FHA, FHC\nHLT")
        assert code == [145, 0x01, 0x41, 0]

    def test_fmov_rr_self(self) -> None:
        """FMOV.F FA, FA -> [145, 0x00, 0x00] (valid, nop)."""
        code = asm_bytes("FMOV.F FA, FA\nHLT")
        assert code == [145, 0x00, 0x00, 0]


# ── FCVT same-format ban ────────────────────────────────────────


class TestFcvtSameFormatBan:
    """FCVT with identical src/dst formats is an assembler error."""

    def test_fcvt_same_h(self) -> None:
        e = asm_error("FCVT.H.H FHA, FHB\nHLT")
        assert "identical" in e.message.lower()

    def test_fcvt_same_f(self) -> None:
        e = asm_error("FCVT.F.F FA, FB\nHLT")
        assert "identical" in e.message.lower()

    def test_fcvt_same_o3(self) -> None:
        e = asm_error("FCVT.O3.O3 FQA, FQB\nHLT")
        assert "identical" in e.message.lower()

    def test_fcvt_different_ok(self) -> None:
        """Cross-format FCVT still works."""
        code = asm_bytes("FCVT.H.F FHA, FA\nHLT")
        assert code == [146, 0x01, 0x00, 0]


class TestIsaEdges:
    def test_validate_fpm_reserved_fmt(self) -> None:
        from pysim8.isa import validate_fpm
        assert validate_fpm(0b00_000_101) is False

    def test_validate_fpm_invalid_pos(self) -> None:
        from pysim8.isa import validate_fpm
        assert validate_fpm(0b00_001_000) is False

    def test_db_unsupported_operand(self) -> None:
        """DB with register operand → error (line 152-153)."""
        e = asm_error("DB A\nHLT", arch=2)
        assert "does not support" in e.message.lower()

    def test_fcvt_missing_src_suffix(self) -> None:
        """FCVT.H with only one suffix → error (line 211)."""
        e = asm_error("FCVT.H FHA, FA\nHLT", arch=2)
        assert "suffix required" in e.message.lower()

    def test_fp_insn_no_suffix(self) -> None:
        """FADD without format suffix → error (line 233)."""
        e = asm_error("FADD FA, [100]\nHLT", arch=2)
        assert "suffix required" in e.message.lower()

    def test_fmov_imm_non_fpreg_dst(self) -> None:
        """FMOV.H with integer register dst → error (line 266)."""
        e = asm_error("FMOV.H A, 1.0\nHLT", arch=2)
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "does not support" in e.message.lower()
        )

    def test_fmov_imm_no_suffix(self) -> None:
        """FMOV FHA, 1.0 without suffix → error (line 270)."""
        e = asm_error("FMOV FHA, 1.0\nHLT", arch=2)
        assert "suffix required" in e.message.lower()

    def test_label_address_over_255(self) -> None:
        """Label beyond 256 bytes → error (line 437)."""
        padding = "DB " + ", ".join(["0"] * 256)
        source = f"{padding}\ntarget:\nHLT\nJMP target\n"
        e = asm_error(source, arch=2)
        assert "must have a value" in e.message.lower()

    def test_operand_matches_fp_imm(self) -> None:
        """FP_IMM8/FP_IMM16 matching (line 67-68)."""
        from pysim8.asm.codegen import _operand_matches
        from pysim8.isa import OpType
        fp_imm = OpFpImm(value=1.0, fmt=None)
        assert _operand_matches(fp_imm, OpType.FP_IMM8)
        assert _operand_matches(fp_imm, OpType.FP_IMM16)
        assert not _operand_matches(OpConst(42), OpType.FP_IMM8)

    def test_db_empty_string(self) -> None:
        """DB with empty string → error (line 137)."""
        e = asm_error('DB ""\nHLT', arch=2)
        assert "must not be empty" in e.message.lower()

    def test_db_float_then_float(self) -> None:
        """DB with multiple floats exercises OpFloat loop-back branch."""
        from pysim8.asm.codegen import _encode_db
        from pysim8.asm.parser import OpFloat
        result = _encode_db([OpFloat(1.0, 0), OpFloat(2.0, 0)], 1)
        assert result == list(struct.pack("<f", 1.0)) + list(struct.pack("<f", 2.0))

    def test_db_unsupported_operand_type(self) -> None:
        """DB with unexpected operand type raises AssemblerError."""
        from pysim8.asm.codegen import _encode_db_operand, AssemblerError
        from pysim8.asm.parser import OpReg
        result: list[int] = []
        with pytest.raises(AssemblerError) as exc_info:
            _encode_db_operand(OpReg(0), 1, result)
        assert "does not support" in str(exc_info.value).lower()

    def test_encode_regaddr_invalid_reg(self) -> None:
        from pysim8.isa import encode_regaddr
        with pytest.raises(ValueError) as exc_info:
            encode_regaddr(6, 0)
        assert "invalid register code" in str(exc_info.value).lower()

    def test_encode_regaddr_offset_out_of_range(self) -> None:
        from pysim8.isa import encode_regaddr
        with pytest.raises(ValueError) as exc_info:
            encode_regaddr(0, 16)
        assert "offset out of range" in str(exc_info.value).lower()


# ── Parser coverage tests ──────────────────────────────────────────


class TestParserCoverage:
    """Tests targeting uncovered parser.py lines."""

    def test_fp_mnemonic_too_many_dots(self) -> None:
        """FMOV.F.H.X should error — 4+ dot parts (line 601)."""
        e = asm_error("FMOV.F.H.X FA\nHLT")
        assert "Syntax error" in e.message

    def test_db_float_n1_unsupported(self) -> None:
        """DB 1.0_n1 rejected — 4-bit format (line 396)."""
        e = asm_error("DB 1.0_n1")
        assert "Unsupported" in e.message or "n1" in e.message.lower()

    def test_db_float_n2_unsupported(self) -> None:
        """DB 1.0_n2 rejected — 4-bit format (line 396)."""
        e = asm_error("DB 1.0_n2")
        assert "Unsupported" in e.message or "n2" in e.message.lower()

    def test_db_float_invalid_suffix(self) -> None:
        """DB 1.0_zz rejected — unknown suffix (line 393)."""
        e = asm_error("DB 1.0_zz")
        assert "Invalid" in e.message or "float" in e.message.lower()

    def test_fmov_imm_negative_nan(self) -> None:
        """FMOV.H FHA, -nan exercises -val path (line 323)."""
        code = asm_bytes("FMOV.H FHA, -nan\nHLT")
        assert code == [162, 0x01, 0x00, 0xFE, 0]

    def test_db_empty_part_between_commas(self) -> None:
        """DB 1,,2 with empty part between commas (line 460)."""
        # The tokenizer strips whitespace; an empty part should be skipped.
        code = asm_bytes("DB 1, , 2")
        assert code == [1, 2]

    def test_string_operand_in_db(self) -> None:
        """DB "hello" exercises _try_string path (line 282)."""
        code = asm_bytes("DB \"XY\"")
        assert code == [ord('X'), ord('Y')]

    def test_fp_suffix_unknown_dot_non_fp(self) -> None:
        """MOV.F A, B — dot in non-FP mnemonic → unknown (line 596→604)."""
        e = asm_error("MOV.F A, B\nHLT")
        assert "Invalid" in e.message or "Syntax" in e.message


# ── FP assembler crazy input tests ─────────────────────────────────


class TestFpCrazyInput:
    """Adversarial FP assembler inputs."""

    def test_fmov_no_operands(self) -> None:
        e = asm_error("FMOV.F\nHLT")
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "does not support" in e.message.lower()
        )

    def test_fmov_one_operand(self) -> None:
        e = asm_error("FMOV.F FA\nHLT")
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "does not support" in e.message.lower()
        )

    def test_fmov_three_operands(self) -> None:
        e = asm_error("FMOV.F FA, [10], [20]\nHLT")
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "too many" in e.message.lower()
        )

    def test_fadd_no_operands(self) -> None:
        e = asm_error("FADD.F\nHLT", arch=2)
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "does not support" in e.message.lower()
        )

    def test_fabs_extra_operand(self) -> None:
        e = asm_error("FABS.F FA, FB\nHLT", arch=2)
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "does not support" in e.message.lower()
            or "too many" in e.message.lower()
        )

    def test_fcvt_three_suffixes(self) -> None:
        """FCVT with 3+ suffixes is a syntax error."""
        e = asm_error("FCVT.H.F.BF FHA, FA\nHLT", arch=2)
        assert (
            "syntax" in e.message.lower()
            or "invalid" in e.message.lower()
            or "does not support" in e.message.lower()
        )

    def test_fmov_imm_float32_reject(self) -> None:
        """FMOV.F FA, 1.5 — float32 imm not supported."""
        e = asm_error("FMOV.F FA, 1.5\nHLT", arch=2)
        assert "not supported" in e.message.lower()

    def test_db_float_int_then_float_error(self) -> None:
        """DB 42, 1.0 — int before float → error (line 472)."""
        e = asm_error("DB 42, 1.0")
        assert "mix" in e.message.lower()

    def test_fcvt_same_format_all(self) -> None:
        """All FCVT same-format combinations rejected."""
        for sfx in ("F", "H", "BF", "O3", "O2"):
            e = asm_error(f"FCVT.{sfx}.{sfx} FA, FA\nHLT", arch=2)
            assert "identical" in e.message.lower()

    def test_fmov_regaddr_load(self) -> None:
        """FMOV.F FA, [B] — register indirect load."""
        code = asm_bytes("FMOV.F FA, [B]\nHLT")
        assert code == [129, 0x00, 0x01, 0]

    def test_fmov_regaddr_store(self) -> None:
        """FMOV.F [B], FA — register indirect store."""
        code = asm_bytes("FMOV.F [B], FA\nHLT")
        assert code == [131, 0x00, 0x01, 0]

    def test_fp_with_label_in_regaddr(self) -> None:
        """FADD.F FA, [B+3] — FP with register indirect + offset."""
        code = asm_bytes("FADD.F FA, [B+3]\nHLT")
        assert code == [133, 0x00, 0x19, 0]

    def test_fmadd_regaddr_encoding(self) -> None:
        """FMADD.F FA, FA, [B] — register indirect in FMADD."""
        code = asm_bytes("FMADD.F FA, FA, [B]\nHLT")
        assert code == [160, 0x00, 0x00, 0x01, 0]


# ── FP assembler property-based tests ──────────────────────────────


class TestPropFpAssembly:
    """Property-based tests for FP assembler."""

    @given(st.sampled_from([
        ("FABS", "FA", 0x00), ("FNEG", "FA", 0x00), ("FSQRT", "FA", 0x00),
        ("FABS", "FHA", 0x01), ("FNEG", "FHB", 0x09),
        ("FABS", "FQA", 0x03), ("FNEG", "FQD", 0x1C),
    ]))
    def test_unary_fpm_encoding(
        self, args: tuple[str, str, int],
    ) -> None:
        """Unary FP instructions: opcode + FPM + HLT."""
        mnem, reg, expected_fpm = args
        fmt = {0x00: "F", 0x01: "H", 0x09: "H", 0x03: "O3", 0x1C: "O2"}[expected_fpm]
        code = asm_bytes(f"{mnem}.{fmt} {reg}\nHLT")
        assert code[1] == expected_fpm

    @given(st.sampled_from(["F", "H", "BF", "O3", "O2", "E8M23", "E5M10"]))
    def test_all_suffixes_accepted(self, sfx: str) -> None:
        """Every documented suffix is accepted by the assembler."""
        reg = {"F": "FA", "H": "FHA", "BF": "FHB", "O3": "FQA",
               "O2": "FQB", "E8M23": "FA", "E5M10": "FHA"}[sfx]
        code = asm_bytes(f"FABS.{sfx} {reg}\nHLT")
        assert code[0] == 142
        assert code[2] == 0


class TestCodegenEdgeCoverage:
    """Tests for codegen.py uncovered lines."""

    def test_operand_matches_returns_false(self) -> None:
        """_operand_matches returns False for unrecognized operand type."""
        from pysim8.asm.codegen import _operand_matches
        from pysim8.asm.parser import OpReg
        # Pass a sentinel that won't match any case branch
        assert _operand_matches(OpReg(0), "NOT_AN_OPTYPE") is False

    def test_encode_operand_unexpected_type(self) -> None:
        """_encode_operand raises on unexpected operand type."""
        from pysim8.asm.codegen import _encode_operand
        from pysim8.asm.parser import OpString
        with pytest.raises(AssertionError) as exc_info:
            _encode_operand(OpString("hi"))
        assert "unexpected operand" in str(exc_info.value).lower()

    def test_find_insn_invalid_fp_mnemonic(self) -> None:
        """_find_insn with FP table raises on invalid mnemonic."""
        from pysim8.asm.codegen import _find_insn, AssemblerError
        from pysim8.isa import BY_MNEMONIC_FP
        with pytest.raises(AssemblerError) as exc_info:
            _find_insn("BOGUS", [], 1, table=BY_MNEMONIC_FP)
        msg = str(exc_info.value).lower()
        assert "invalid instruction" in msg and "bogus" in msg
