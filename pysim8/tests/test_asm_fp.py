"""FP assembler tests for arch=2.

Tests verify FP instruction encoding, DB float literals, and error
handling. All tests use arch=2 unless explicitly testing arch=1
regression.
"""

from __future__ import annotations

import struct

import pytest

from pysim8.asm import assemble, AssemblerError


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
