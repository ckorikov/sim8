"""CPU simulator tests from spec/tests.md (tests 1-109, 152-181).

Tests are organized by spec sections. Each test assembles source code,
executes it on the CPU, and verifies the resulting state.
"""

import pytest

from pysim8.asm import AssemblerError, assemble
from pysim8.sim import CPU, CpuState, ErrorCode, list_tracer


# ── helpers ──────────────────────────────────────────────────────────


def run(source: str) -> CPU:
    """Assemble source, load into CPU, run until halt/fault."""
    result = assemble(source)
    cpu = CPU()
    cpu.load(result.code)
    state = cpu.run()
    assert state != CpuState.RUNNING, "Step limit reached — infinite loop?"
    return cpu


def run_fault(source: str, code: int) -> CPU:
    """Assemble source, run, assert FAULT with given error code."""
    cpu = run(source)
    assert cpu.state == CpuState.FAULT, f"Expected FAULT, got {cpu.state}"
    assert cpu.fault is True
    assert cpu.a == code, f"Expected A={code}, got A={cpu.a}"
    return cpu


# ── 5.2 MOV — Data Movement (tests 1-9) ─────────────────────────────


class TestMov:
    """Spec §5.2 — MOV opcodes 1-8."""

    def test_01_mov_const_and_reg_reg(self) -> None:
        cpu = run("MOV A, 42\nMOV B, A\nHLT")
        assert cpu.a == 42
        assert cpu.b == 42

    def test_02_chain_copy(self) -> None:
        cpu = run("MOV A, 0xFF\nMOV B, A\nMOV C, B\nMOV D, C\nHLT")
        assert cpu.a == 255
        assert cpu.b == 255
        assert cpu.c == 255
        assert cpu.d == 255

    def test_03_mov_sp(self) -> None:
        cpu = run("MOV SP, 200\nMOV A, SP\nHLT")
        assert cpu.sp == 200
        assert cpu.a == 200

    def test_04_mov_addr(self) -> None:
        cpu = run("MOV A, 77\nMOV [0x50], A\nMOV B, [0x50]\nHLT")
        assert cpu.mem[0x50] == 77
        assert cpu.b == 77

    def test_05_mov_addr_const(self) -> None:
        cpu = run("MOV [0x50], 99\nMOV A, [0x50]\nHLT")
        assert cpu.mem[0x50] == 99
        assert cpu.a == 99

    def test_06_mov_regaddr(self) -> None:
        cpu = run("MOV B, 0x50\nMOV A, 33\nMOV [B], A\nMOV C, [B]\nHLT")
        assert cpu.mem[0x50] == 33
        assert cpu.c == 33

    def test_07_mov_regaddr_offset(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [B+2], 88\nMOV A, [B+2]\nHLT")
        assert cpu.mem[0x52] == 88
        assert cpu.a == 88

    def test_08_flag_preservation_carry(self) -> None:
        cpu = run("MOV A, 255\nADD A, 1\nMOV B, 42\nHLT")
        assert cpu.carry is True

    def test_09_flag_preservation_zero(self) -> None:
        cpu = run("MOV A, 1\nSUB A, 1\nMOV B, 99\nHLT")
        assert cpu.zero is True


# ── 5.3 ADD / SUB — Arithmetic (tests 10-20) ────────────────────────


class TestAddSub:
    """Spec §5.3 — ADD/SUB opcodes 10-17."""

    def test_10_add_reg_reg(self) -> None:
        cpu = run("MOV A, 3\nMOV B, 5\nADD A, B\nHLT")
        assert cpu.a == 8
        assert cpu.zero is False
        assert cpu.carry is False

    def test_11_add_reg_const(self) -> None:
        cpu = run("MOV A, 10\nADD A, 20\nHLT")
        assert cpu.a == 30

    def test_12_sub_reg_reg(self) -> None:
        cpu = run("MOV A, 10\nMOV B, 3\nSUB A, B\nHLT")
        assert cpu.a == 7
        assert cpu.carry is False

    def test_13_sub_underflow(self) -> None:
        cpu = run("MOV A, 10\nSUB A, 20\nHLT")
        assert cpu.a == 246
        assert cpu.carry is True

    def test_14_add_overflow(self) -> None:
        cpu = run("MOV A, 200\nADD A, 100\nHLT")
        assert cpu.a == 44
        assert cpu.carry is True

    def test_15_sub_zero_minus_one(self) -> None:
        cpu = run("MOV A, 0\nSUB A, 1\nHLT")
        assert cpu.a == 255
        assert cpu.carry is True

    def test_16_add_overflow_to_zero(self) -> None:
        cpu = run("MOV A, 128\nADD A, 128\nHLT")
        assert cpu.a == 0
        assert cpu.carry is True
        assert cpu.zero is True

    def test_17_add_sp(self) -> None:
        cpu = run("MOV SP, 100\nADD SP, 10\nHLT")
        assert cpu.sp == 110

    def test_18_sub_sp(self) -> None:
        cpu = run("MOV SP, 100\nMOV A, 30\nSUB SP, A\nHLT")
        assert cpu.sp == 70

    def test_19_add_from_addr(self) -> None:
        cpu = run("MOV [0x50], 25\nMOV A, 10\nADD A, [0x50]\nHLT")
        assert cpu.a == 35

    def test_20_add_from_regaddr(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [0x50], 7\nMOV A, 3\nADD A, [B]\nHLT")
        assert cpu.a == 10

    def test_sub_from_regaddr(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [0x50], 3\nMOV A, 10\nSUB A, [B]\nHLT")
        assert cpu.a == 7


# ── 5.4 INC / DEC (tests 21-25) ─────────────────────────────────────


class TestIncDec:
    """Spec §5.4 — INC/DEC opcodes 18-19."""

    def test_21_inc_basic(self) -> None:
        cpu = run("MOV A, 0\nINC A\nHLT")
        assert cpu.a == 1
        assert cpu.zero is False
        assert cpu.carry is False

    def test_22_inc_overflow(self) -> None:
        cpu = run("MOV A, 255\nINC A\nHLT")
        assert cpu.a == 0
        assert cpu.carry is True

    def test_23_dec_to_zero(self) -> None:
        cpu = run("MOV A, 1\nDEC A\nHLT")
        assert cpu.a == 0
        assert cpu.zero is True

    def test_24_dec_underflow(self) -> None:
        cpu = run("MOV A, 0\nDEC A\nHLT")
        assert cpu.a == 255
        assert cpu.carry is True

    def test_25_inc_sp(self) -> None:
        cpu = run("INC SP\nHLT")
        assert cpu.sp == 232


# ── 5.5 CMP — Compare (tests 26-29) ─────────────────────────────────


class TestCmp:
    """Spec §5.5 — CMP opcodes 20-23."""

    def test_26_equal(self) -> None:
        cpu = run("MOV A, 5\nCMP A, 5\nHLT")
        assert cpu.zero is True
        assert cpu.carry is False
        assert cpu.a == 5

    def test_27_less_than(self) -> None:
        cpu = run("MOV A, 3\nCMP A, 10\nHLT")
        assert cpu.zero is False
        assert cpu.carry is True
        assert cpu.a == 3

    def test_28_greater_than(self) -> None:
        cpu = run("MOV A, 10\nCMP A, 3\nHLT")
        assert cpu.zero is False
        assert cpu.carry is False
        assert cpu.a == 10

    def test_29_zero_equals_zero(self) -> None:
        cpu = run("MOV A, 0\nCMP A, 0\nHLT")
        assert cpu.zero is True
        assert cpu.carry is False

    def test_cmp_reg_reg(self) -> None:
        cpu = run("MOV A, 5\nMOV B, 5\nCMP A, B\nHLT")
        assert cpu.zero is True
        assert cpu.a == 5  # CMP doesn't modify dest

    def test_cmp_regaddr(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [0x50], 5\nMOV A, 5\nCMP A, [B]\nHLT")
        assert cpu.zero is True

    def test_cmp_addr(self) -> None:
        cpu = run("MOV [0x50], 3\nMOV A, 10\nCMP A, [0x50]\nHLT")
        assert cpu.zero is False
        assert cpu.carry is False  # A > [0x50]


# ── 5.6 JMP / Conditional Jumps (tests 30-38) ───────────────────────


class TestJumps:
    """Spec §5.6 — JMP/Jcc opcodes 30-43."""

    def test_30_jmp_addr(self) -> None:
        cpu = run("JMP end\nMOV A, 99\nend: HLT")
        assert cpu.a == 0

    def test_31_jmp_reg(self) -> None:
        cpu = run("MOV B, end\nJMP B\nMOV A, 99\nend: HLT")
        assert cpu.a == 0

    def test_32_jz_taken(self) -> None:
        cpu = run("MOV A, 5\nCMP A, 5\nJZ equal\nMOV B, 1\nequal: HLT")
        assert cpu.b == 0

    def test_33_jz_not_taken(self) -> None:
        cpu = run("MOV A, 5\nCMP A, 3\nJZ skip\nMOV B, 1\nskip: HLT")
        assert cpu.b == 1

    def test_34_jnz_taken(self) -> None:
        cpu = run("MOV A, 5\nCMP A, 3\nJNZ notzero\nMOV B, 1\nnotzero: HLT")
        assert cpu.b == 0

    def test_35_jc_taken(self) -> None:
        cpu = run("MOV A, 200\nADD A, 100\nJC overflow\nMOV B, 1\noverflow: HLT")
        assert cpu.b == 0

    def test_36_jnc_taken(self) -> None:
        cpu = run("MOV A, 5\nADD A, 3\nJNC nocarry\nMOV B, 1\nnocarry: HLT")
        assert cpu.b == 0

    def test_37_ja_taken(self) -> None:
        cpu = run("MOV A, 10\nCMP A, 3\nJA above\nMOV B, 1\nabove: HLT")
        assert cpu.b == 0

    def test_38_jna_taken(self) -> None:
        cpu = run("MOV A, 3\nCMP A, 10\nJNA notabove\nMOV B, 1\nnotabove: HLT")
        assert cpu.b == 0


# ── 5.7 Stack Operations — PUSH / POP (tests 45-51) ─────────────────


class TestStack:
    """Spec §5.7 — PUSH/POP opcodes 50-54."""

    def test_45_push_const(self) -> None:
        cpu = run("PUSH 42\nHLT")
        assert cpu.mem[231] == 42
        assert cpu.sp == 230

    def test_46_push_reg(self) -> None:
        cpu = run("MOV A, 77\nPUSH A\nHLT")
        assert cpu.mem[231] == 77
        assert cpu.sp == 230

    def test_47_lifo(self) -> None:
        cpu = run("PUSH 10\nPUSH 20\nPOP A\nPOP B\nHLT")
        assert cpu.a == 20
        assert cpu.b == 10
        assert cpu.sp == 231

    def test_48_push_regaddr(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [0x50], 88\nPUSH [B]\nHLT")
        assert cpu.mem[231] == 88

    def test_49_push_addr(self) -> None:
        cpu = run("PUSH [0x50]\nHLT")
        # mem[0x50] is 0 initially; just test no crash + correct SP
        assert cpu.sp == 230

    def test_50_stack_overflow(self) -> None:
        # SP=0 means no room to push → FAULT(2)
        run_fault("MOV SP, 0\nPUSH 1", ErrorCode.STACK_OVERFLOW)

    def test_51_stack_underflow(self) -> None:
        run_fault("POP A", ErrorCode.STACK_UNDERFLOW)


# ── 5.8 CALL / RET — Subroutines (tests 52-56) ─────────────────────


class TestCallRet:
    """Spec §5.8 — CALL/RET opcodes 55-57."""

    def test_52_basic_call(self) -> None:
        cpu = run("CALL func\nHLT\nfunc: MOV A, 42\nRET")
        assert cpu.a == 42

    def test_53_stack_consistent(self) -> None:
        cpu = run("PUSH 10\nCALL func\nPOP A\nHLT\nfunc: RET")
        assert cpu.a == 10
        assert cpu.sp == 231

    def test_54_nested_calls(self) -> None:
        cpu = run("CALL f1\nHLT\nf1: CALL f2\nINC A\nRET\nf2: MOV A, 1\nRET")
        assert cpu.a == 2

    def test_55_call_reg(self) -> None:
        cpu = run("MOV B, func\nCALL B\nHLT\nfunc: MOV A, 77\nRET")
        assert cpu.a == 77

    def test_56_return_address(self) -> None:
        cpu = run("CALL func\nMOV A, 99\nHLT\nfunc: RET")
        assert cpu.a == 99


# ── 5.9 MUL / DIV (tests 57-66) ─────────────────────────────────────


class TestMulDiv:
    """Spec §5.9 — MUL/DIV opcodes 60-67."""

    def test_57_mul_reg(self) -> None:
        cpu = run("MOV A, 6\nMOV B, 7\nMUL B\nHLT")
        assert cpu.a == 42

    def test_58_mul_overflow(self) -> None:
        cpu = run("MOV A, 200\nMUL 2\nHLT")
        assert cpu.a == 144
        assert cpu.carry is True

    def test_59_div_reg(self) -> None:
        cpu = run("MOV A, 20\nMOV B, 4\nDIV B\nHLT")
        assert cpu.a == 5

    def test_60_div_truncate(self) -> None:
        cpu = run("MOV A, 7\nDIV 2\nHLT")
        assert cpu.a == 3

    def test_61_div_zero(self) -> None:
        run_fault("MOV A, 10\nDIV 0", ErrorCode.DIV_ZERO)

    def test_62_mul_zero_result(self) -> None:
        cpu = run("MOV A, 0\nMUL 100\nHLT")
        assert cpu.a == 0
        assert cpu.zero is True

    def test_63_mul_regaddr(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [0x50], 7\nMOV A, 6\nMUL [B]\nHLT")
        assert cpu.a == 42

    def test_64_mul_addr(self) -> None:
        cpu = run("MOV [0x50], 5\nMOV A, 8\nMUL [0x50]\nHLT")
        assert cpu.a == 40

    def test_65_div_regaddr(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [0x50], 4\nMOV A, 20\nDIV [B]\nHLT")
        assert cpu.a == 5

    def test_66_div_addr(self) -> None:
        cpu = run("MOV [0x50], 3\nMOV A, 15\nDIV [0x50]\nHLT")
        assert cpu.a == 5

    def test_div_zero_via_addr(self) -> None:
        run_fault("MOV A, 10\nDIV [0x50]", ErrorCode.DIV_ZERO)

    def test_div_zero_via_regaddr(self) -> None:
        run_fault("MOV B, 0x50\nMOV A, 10\nDIV [B]", ErrorCode.DIV_ZERO)


# ── 5.10 Bitwise — AND / OR / XOR / NOT (tests 67-72) ───────────────


class TestBitwise:
    """Spec §5.10 — Bitwise opcodes 70-82."""

    def test_67_and(self) -> None:
        cpu = run("MOV A, 0xFF\nAND A, 0x0F\nHLT")
        assert cpu.a == 0x0F
        assert cpu.carry is False

    def test_68_or(self) -> None:
        cpu = run("MOV A, 0xF0\nOR A, 0x0F\nHLT")
        assert cpu.a == 0xFF
        assert cpu.carry is False

    def test_69_xor_self(self) -> None:
        cpu = run("MOV A, 0xFF\nXOR A, 0xFF\nHLT")
        assert cpu.a == 0
        assert cpu.zero is True
        assert cpu.carry is False

    def test_70_not_zero(self) -> None:
        cpu = run("MOV A, 0\nNOT A\nHLT")
        assert cpu.a == 255
        assert cpu.carry is False

    def test_71_not_0f(self) -> None:
        cpu = run("MOV A, 0x0F\nNOT A\nHLT")
        assert cpu.a == 0xF0
        assert cpu.carry is False

    def test_72_not_ff(self) -> None:
        cpu = run("MOV A, 0xFF\nNOT A\nHLT")
        assert cpu.a == 0
        assert cpu.zero is True
        assert cpu.carry is False


# ── 5.11 Shift — SHL / SHR (tests 73-80) ────────────────────────────


class TestShift:
    """Spec §5.11 — SHL/SHR opcodes 90-97."""

    def test_73_shl_1(self) -> None:
        cpu = run("MOV A, 1\nSHL A, 1\nHLT")
        assert cpu.a == 2

    def test_74_shl_7(self) -> None:
        cpu = run("MOV A, 1\nSHL A, 7\nHLT")
        assert cpu.a == 128

    def test_75_shl_overflow(self) -> None:
        cpu = run("MOV A, 128\nSHL A, 1\nHLT")
        assert cpu.a == 0
        assert cpu.carry is True

    def test_76_shr_1(self) -> None:
        cpu = run("MOV A, 128\nSHR A, 1\nHLT")
        assert cpu.a == 64

    def test_77_shr_bit_out(self) -> None:
        cpu = run("MOV A, 1\nSHR A, 1\nHLT")
        assert cpu.a == 0
        assert cpu.zero is True
        assert cpu.carry is True

    def test_78_sal_alias(self) -> None:
        cpu = run("MOV A, 3\nSAL A, 2\nHLT")
        assert cpu.a == 12

    def test_79_sar_alias(self) -> None:
        cpu = run("MOV A, 12\nSAR A, 2\nHLT")
        assert cpu.a == 3

    def test_80_shift_by_zero(self) -> None:
        cpu = run("MOV A, 200\nADD A, 100\nSHL A, 0\nHLT")
        assert cpu.a == 44
        assert cpu.carry is True  # C preserved from ADD


# ── 5.12 Addressing Modes (tests 81-84) ─────────────────────────────


class TestAddressing:
    """Spec §5.12 — cross-instruction addressing mode tests."""

    def test_81_regaddr_offsets(self) -> None:
        cpu = run(
            "MOV B, 0x50\n"
            "MOV [B+0], 10\n"
            "MOV [B+5], 20\n"
            "MOV [B-3], 30\n"
            "HLT"
        )
        assert cpu.mem[0x50] == 10
        assert cpu.mem[0x55] == 20
        assert cpu.mem[0x4D] == 30

    def test_82_sp_relative(self) -> None:
        cpu = run("MOV [SP-1], 42\nMOV A, [SP-1]\nHLT")
        assert cpu.mem[230] == 42
        assert cpu.a == 42

    def test_83_max_positive_offset(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [B+15], 1\nMOV A, [B+15]\nHLT")
        assert cpu.mem[0x5F] == 1
        assert cpu.a == 1

    def test_84_max_negative_offset(self) -> None:
        cpu = run("MOV B, 0x50\nMOV [B-16], 2\nMOV A, [B-16]\nHLT")
        assert cpu.mem[0x40] == 2
        assert cpu.a == 2


# ── 5.13 Flags (tests 85-89) ────────────────────────────────────────


class TestFlags:
    """Spec §5.13 — arithmetic flag corner cases."""

    def test_85_positive_no_flags(self) -> None:
        cpu = run("MOV A, 5\nADD A, 0\nHLT")
        assert cpu.zero is False
        assert cpu.carry is False

    def test_86_zero_result(self) -> None:
        cpu = run("MOV A, 0\nADD A, 0\nHLT")
        assert cpu.zero is True
        assert cpu.carry is False

    def test_87_overflow_to_zero(self) -> None:
        cpu = run("MOV A, 255\nADD A, 1\nHLT")
        assert cpu.a == 0
        assert cpu.zero is True
        assert cpu.carry is True

    def test_88_underflow(self) -> None:
        cpu = run("MOV A, 0\nSUB A, 1\nHLT")
        assert cpu.zero is False
        assert cpu.carry is True

    def test_89_128_plus_128(self) -> None:
        cpu = run("MOV A, 128\nADD A, 128\nHLT")
        assert cpu.a == 0
        assert cpu.carry is True
        assert cpu.zero is True


# ── 5.14 SP Restrictions (tests 90-105) ─────────────────────────────


class TestSPRestrict:
    """Spec §5.14 — SP operand allowed/rejected tests."""

    # Allowed (90-95)
    def test_90_mov_sp(self) -> None:
        cpu = run("MOV SP, 100\nHLT")
        assert cpu.sp == 100

    def test_91_add_sp(self) -> None:
        cpu = run("MOV SP, 100\nADD SP, 10\nHLT")
        assert cpu.sp == 110

    def test_92_sub_sp(self) -> None:
        cpu = run("MOV SP, 100\nSUB SP, 5\nHLT")
        assert cpu.sp == 95

    def test_93_inc_sp(self) -> None:
        cpu = run("INC SP\nHLT")
        assert cpu.sp == 232

    def test_94_dec_sp(self) -> None:
        cpu = run("DEC SP\nHLT")
        assert cpu.sp == 230

    def test_95_cmp_sp(self) -> None:
        cpu = run("CMP SP, 231\nHLT")
        assert cpu.zero is True

    # Rejected (96-105): assembler rejects these, so they produce AssemblerError.
    # We test that they don't silently pass.
    def test_96_push_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("PUSH SP")

    def test_97_pop_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("POP SP")

    def test_98_and_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("AND SP, 0xFF")

    def test_99_or_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("OR SP, 0")

    def test_100_xor_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("XOR SP, SP")

    def test_101_not_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("NOT SP")

    def test_102_shl_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("SHL SP, 1")

    def test_103_shr_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("SHR SP, 1")

    def test_104_mul_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("MUL SP")

    def test_105_div_sp_rejected(self) -> None:
        with pytest.raises(AssemblerError):
            assemble("DIV SP")


# ── 5.15 I/O (tests 106-109) ────────────────────────────────────────


class TestIO:
    """Spec §5.15 — memory-mapped console I/O."""

    def test_106_write_display(self) -> None:
        cpu = run("MOV [232], 72\nMOV [233], 105\nHLT")
        assert cpu.mem[232] == 72  # 'H'
        assert cpu.mem[233] == 105  # 'i'
        assert cpu.display() == "Hi"

    def test_107_write_last_cell(self) -> None:
        cpu = run("MOV A, 65\nMOV [0xFF], A\nHLT")
        assert cpu.mem[255] == 65

    def test_108_read_display(self) -> None:
        cpu = run("MOV A, [232]\nHLT")
        assert cpu.a == cpu.mem[232]

    def test_109_dp_not_zero(self) -> None:
        cpu = run("MOV DP, 5\nMOV [232], 72\nHLT")
        assert cpu.mem[5 * 256 + 232] == 72
        assert cpu.display() == ""  # I/O region only on page 0


# ── 5.19 Integration — End-to-End Programs (tests 152-156) ──────────


class TestIntegration:
    """Spec §5.19 — full programs."""

    def test_152_counter(self) -> None:
        cpu = run("MOV A, 0\nloop: INC A\nCMP A, 5\nJNZ loop\nHLT")
        assert cpu.a == 5

    def test_153_sum_1_to_10(self) -> None:
        cpu = run(
            "MOV A, 0\n"
            "MOV B, 1\n"
            "loop: ADD A, B\n"
            "INC B\n"
            "CMP B, 11\n"
            "JNZ loop\n"
            "HLT"
        )
        assert cpu.a == 55

    def test_154_factorial_5(self) -> None:
        cpu = run(
            "MOV A, 1\n"
            "MOV B, 5\n"
            "loop: MUL B\n"
            "DEC B\n"
            "CMP B, 1\n"
            "JA loop\n"
            "HLT"
        )
        assert cpu.a == 120

    def test_155_hello(self) -> None:
        cpu = run(
            "MOV A, 0\n"
            "MOV B, 232\n"
            "MOV C, hello\n"
            ".loop: MOV A, [C]\n"
            "CMP A, 0\n"
            "JZ .end\n"
            "MOV [B], A\n"
            "INC B\n"
            "INC C\n"
            "JMP .loop\n"
            '.end: HLT\n'
            'hello: DB "Hello"\n'
            "DB 0"
        )
        assert cpu.display() == "Hello"

    def test_156_stack_frame(self) -> None:
        cpu = run(
            "PUSH 10\n"
            "PUSH 20\n"
            "CALL add_two\n"
            "HLT\n"
            "add_two:\n"
            "MOV A, [SP+2]\n"
            "ADD A, [SP+3]\n"
            "RET"
        )
        assert cpu.a == 30


# ── 5.21 DP Register (tests 161-170) ────────────────────────────────


class TestDP:
    """Spec §5.21 — paged memory access via DP."""

    def test_161_basic_dp(self) -> None:
        cpu = run("MOV DP, 0\nMOV A, DP\nHLT")
        assert cpu.dp == 0
        assert cpu.a == 0

    def test_162_max_dp(self) -> None:
        cpu = run("MOV DP, 255\nHLT")
        assert cpu.dp == 255

    def test_163_page_128(self) -> None:
        cpu = run("MOV DP, 128\nMOV B, 0\nMOV [B], 42\nHLT")
        assert cpu.mem[0x8000] == 42

    def test_164_page_0_regaddr(self) -> None:
        cpu = run("MOV DP, 0\nMOV B, 0x50\nMOV [B], 42\nHLT")
        assert cpu.mem[0x050] == 42

    def test_165_page_1(self) -> None:
        cpu = run("MOV DP, 1\nMOV B, 0x50\nMOV [B], 99\nMOV A, [B]\nHLT")
        assert cpu.mem[0x150] == 99
        assert cpu.a == 99

    def test_166_page_2_offset(self) -> None:
        cpu = run("MOV DP, 2\nMOV B, 0\nMOV [B+10], 77\nHLT")
        assert cpu.mem[0x20A] == 77

    def test_167_direct_uses_dp(self) -> None:
        cpu = run(
            "MOV [0x50], 11\n"
            "MOV DP, 1\n"
            "MOV [0x50], 22\n"
            "MOV A, [0x50]\n"
            "MOV DP, 0\n"
            "MOV B, [0x50]\n"
            "HLT"
        )
        assert cpu.mem[0x50] == 11
        assert cpu.mem[0x150] == 22
        assert cpu.a == 22
        assert cpu.b == 11

    def test_168_sp_relative_ignores_dp(self) -> None:
        cpu = run("MOV DP, 1\nMOV [SP-1], 55\nMOV A, [SP-1]\nHLT")
        assert cpu.mem[230] == 55
        assert cpu.a == 55

    def test_169_page_boundary_with_dp(self) -> None:
        run_fault("MOV DP, 1\nMOV B, 250\nMOV [B+10], 33", ErrorCode.PAGE_BOUNDARY)

    def test_170_cross_page_copy(self) -> None:
        cpu = run(
            "MOV DP, 1\n"
            "MOV B, 0\n"
            "MOV [B], 0xAA\n"
            "MOV A, [B]\n"
            "MOV DP, 2\n"
            "MOV [B], A\n"
            "HLT"
        )
        assert cpu.mem[0x200] == 0xAA


# ── 5.22 Robustness (tests 171-181) ─────────────────────────────────


class TestRobustness:
    """Spec §5.22 — adversarial scenarios."""

    def test_171_self_modifying_code(self) -> None:
        cpu = run("MOV [20], 0\nJMP 20\nMOV A, 255\nHLT")
        assert cpu.ip == 20
        assert cpu.state == CpuState.HALTED
        assert cpu.a == 0

    def test_172_empty_stack_pop(self) -> None:
        run_fault("POP A", ErrorCode.STACK_UNDERFLOW)

    def test_173_stack_overflow(self) -> None:
        # SP=0 means no room to push → FAULT(2)
        run_fault("MOV SP, 0\nPUSH 1", ErrorCode.STACK_OVERFLOW)

    def test_174_invalid_opcode_9(self) -> None:
        run_fault("DB 9", ErrorCode.INVALID_OPCODE)

    def test_175_invalid_opcode_99(self) -> None:
        run_fault("DB 99", ErrorCode.INVALID_OPCODE)

    def test_176_div_zero_self(self) -> None:
        run_fault("DIV A", ErrorCode.DIV_ZERO)

    def test_177_div_zero_reg(self) -> None:
        run_fault("MOV B, 0\nDIV B", ErrorCode.DIV_ZERO)

    def test_178_invalid_reg_code_6(self) -> None:
        run_fault("DB 70, 6, 0", ErrorCode.INVALID_REG)

    def test_179_not_dp_invalid(self) -> None:
        run_fault("DB 82, 5", ErrorCode.INVALID_REG)

    def test_180_code_overwrite_via_stack(self) -> None:
        # PUSH writes HLT (0) to addr 10, overwriting MOV A, 99.
        # MOV A, 42 executes, JMP 10 lands on the overwritten HLT.
        cpu = run(
            "MOV SP, 10\n"   # SP points into code area
            "PUSH 0\n"       # writes HLT (0) to addr 10
            "MOV A, 42\n"    # addr 5-7, executes normally
            "JMP 10\n"       # addr 8-9, jump to overwritten HLT
            "MOV A, 99\n"    # addr 10-12, but addr 10 is now HLT
        )
        assert cpu.a == 42

    def test_181_exec_from_high_memory(self) -> None:
        cpu = run(
            "MOV [200], 6\n"   # MOV opcode
            "MOV [201], 0\n"   # reg A
            "MOV [202], 77\n"  # value 77
            "MOV [203], 0\n"   # HLT
            "JMP 200"
        )
        assert cpu.a == 77
        assert cpu.ip == 203

    def test_page_boundary_fault(self) -> None:
        # 3-byte instruction (MOV REG, CONST = opcode 6) at addr 254 crosses page
        cpu = CPU()
        code = [0] * 254 + [6, 0, 42]  # would need bytes 254,255,256
        cpu.load(code)
        cpu.regs.ip = 254
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.PAGE_BOUNDARY

    def test_display_nonprintable_filtered(self) -> None:
        cpu = run("MOV [232], 1\nMOV [233], 65\nHLT")
        assert cpu.display() == " A"  # byte 1 → space, 65 → 'A'


# ── Lifecycle (reset, step-after-halt, max_steps) ────────────────────


class TestLifecycle:
    """CPU lifecycle: reset, re-run, step limits."""

    def test_reset_after_fault(self) -> None:
        cpu = CPU()
        cpu.load(assemble("DB 9").code)  # invalid opcode → FAULT
        cpu.run()
        assert cpu.state == CpuState.FAULT
        # Reset and run new code
        cpu.load(assemble("MOV A, 42\nHLT").code)
        cpu.run()
        assert cpu.state == CpuState.HALTED
        assert cpu.a == 42

    def test_step_after_halt(self) -> None:
        cpu = run("HLT")
        assert cpu.state == CpuState.HALTED
        assert cpu.step() is False

    def test_step_after_fault(self) -> None:
        cpu = CPU()
        cpu.load(assemble("DB 9").code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.step() is False

    def test_run_max_steps(self) -> None:
        cpu = CPU()
        cpu.load(assemble("loop: JMP loop").code)
        state = cpu.run(max_steps=10)
        assert state == CpuState.RUNNING


# ── Tracing ──────────────────────────────────────────────────────────


class TestTracing:
    """TraceEvent emission and tracer callbacks."""

    def test_list_tracer_basic(self) -> None:
        events, cb = list_tracer()
        cpu = CPU(tracer=cb)
        cpu.load(assemble("MOV A, 42\nHLT").code)
        cpu.run()
        assert len(events) == 1
        assert events[0].ip == 0
        assert events[0].is_fault is False

    def test_tracer_fault_event(self) -> None:
        events, cb = list_tracer()
        cpu = CPU(tracer=cb)
        cpu.load(assemble("DB 9").code)
        cpu.run()
        assert len(events) == 1
        assert events[0].is_fault is True

    def test_tracer_records_changes(self) -> None:
        events, cb = list_tracer()
        cpu = CPU(tracer=cb)
        cpu.load(assemble("MOV A, 42\nHLT").code)
        cpu.run()
        assert "A" in events[0].changes
        assert events[0].changes["A"] == 42
