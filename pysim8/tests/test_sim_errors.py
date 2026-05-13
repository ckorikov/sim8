"""Error code and fault state machine tests from spec/tests/tests-errors.md (E1-E29)."""

from __future__ import annotations

import pytest
from conftest import run

from pysim8.asm import assemble
from pysim8.isa import Op, VU_FMT_U, VU_MODE_VV, encode_vfm, encode_vu_regs
from pysim8.sim import CPU, CpuState
from pysim8.sim.errors import ErrorCode
from pysim8.sim.registers import FpuRegisters


def _run_fault(source: str, arch: int = 1) -> CPU:
    cpu = run(source, arch=arch)
    assert cpu.state == CpuState.FAULT
    return cpu


def _run_fp(source: str) -> CPU:
    result = assemble(source, arch=2)
    cpu = CPU(arch=2)
    cpu.load(result.code)
    cpu.run()
    return cpu


def _run_vu(source: str) -> tuple[CPU, dict[str, int]]:
    result = assemble(source, arch=3)
    cpu = CPU(arch=3)
    cpu.load(result.code)
    cpu.run()
    return cpu, result.labels


# ── E.1 Error Code Values ────────────────────────────────────────────


class TestErrorCodeValues:
    """Spec §E.1 — each ERR_* condition produces the correct code."""

    def test_e1_div_zero(self) -> None:
        cpu = _run_fault("MOV A, 0\nDIV A\nHLT")
        assert cpu.a == int(ErrorCode.DIV_ZERO)

    def test_e2_stack_overflow(self) -> None:
        cpu = _run_fault("MOV SP, 0\nPUSH A\nHLT")
        assert cpu.a == int(ErrorCode.STACK_OVERFLOW)

    def test_e3_stack_underflow(self) -> None:
        cpu = _run_fault("POP A\nHLT")
        assert cpu.a == int(ErrorCode.STACK_UNDERFLOW)

    def test_e4_invalid_reg(self) -> None:
        cpu = _run_fault("DB 70, 6, 0\nHLT")  # opcode 70, invalid reg=6
        assert cpu.a == int(ErrorCode.INVALID_REG)

    def test_e5_page_boundary(self) -> None:
        cpu = _run_fault("MOV B, 250\nMOV A, [B+15]")
        assert cpu.a == int(ErrorCode.PAGE_BOUNDARY)

    def test_e6_invalid_opcode(self) -> None:
        cpu = _run_fault("DB 9\nHLT")  # opcode 9 is unassigned
        assert cpu.a == int(ErrorCode.INVALID_OPCODE)

    def test_e7_fp_format(self) -> None:
        cpu = CPU(arch=2)
        cpu.load([int(Op.FABS_FP), 0x07, int(Op.HLT)])  # FPM fmt=7 reserved
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.FP_FORMAT)

    def test_e8_vu_oob(self) -> None:
        # VA=0xFFFF, VL=2, UINT8: 0xFFFF+2=0x10001 > MEM_SIZE → OOB
        cpu = CPU(arch=3)
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)
        code = (
            [163, 0, 0xFF, 0xFF]  # VSET VA, 0xFFFF
            + [163, 4, 2, 0]  # VSET VL, 2
            + [int(Op.VADD), vfm_enc, encode_vu_regs(2, 0, 1)]  # VADD.U VC, VA, VB (3 bytes)
            + [int(Op.VWAIT), int(Op.HLT)]
        )
        cpu.load(code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.VU_OOB)

    def test_e9_vu_format_vdot_int(self) -> None:
        cpu = CPU(arch=3)
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)  # UINT8 — invalid for VDOT
        code = (
            [163, 4, 4, 0]  # VSET VL, 4
            + [int(Op.VDOT), vfm_enc, encode_vu_regs(2, 0, 1), 0]
            + [int(Op.VWAIT), int(Op.HLT)]
        )
        cpu.load(code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.VU_FORMAT)


# ── E.2 Fault State Machine Invariants ──────────────────────────────


class TestFaultStateMachine:
    """Spec §E.2 — fault sets F=1, freezes IP, preserves Z/C."""

    def test_e10_f_flag_set_and_a_is_code(self) -> None:
        cpu = _run_fault("MOV A, 0\nDIV A\nHLT")
        assert cpu.fault is True
        assert cpu.a == int(ErrorCode.DIV_ZERO)

    def test_e11_original_a_overwritten_by_code(self) -> None:
        # A=42 before fault; error code (1) overwrites it
        cpu = _run_fault("MOV A, 42\nMOV B, 0\nDIV B\nHLT")
        assert cpu.a == int(ErrorCode.DIV_ZERO)

    def test_e12_no_fault_f_stays_clear(self) -> None:
        cpu = run("HLT")
        assert cpu.fault is False
        assert cpu.a == 0

    def test_e13_z_and_c_preserved_after_fault(self) -> None:
        # ADD A, A with A=0 → Z=1, C=0; then DIV 0 faults
        cpu = _run_fault("MOV A, 0\nADD A, A\nDIV A\nHLT")
        assert cpu.zero is True
        assert cpu.carry is False
        assert cpu.fault is True

    def test_e14_carry_preserved_after_fault(self) -> None:
        # MOV A, 0xFF; ADD A, 1 → Z=1 (wraps to 0), C=1; then DIV 0 faults
        cpu = _run_fault("MOV A, 0xFF\nADD A, 1\nDIV A\nHLT")
        assert cpu.zero is True
        assert cpu.carry is True
        assert cpu.fault is True

    def test_e15_cmp_flags_preserved_after_fault(self) -> None:
        # CMP A, 2 with A=1 → Z=0, C=1; then stack overflow
        cpu = _run_fault("MOV A, 1\nCMP A, 2\nMOV SP, 0\nPUSH A\nHLT")
        assert cpu.zero is False
        assert cpu.carry is True
        assert cpu.fault is True

    def test_e16_ip_frozen_at_faulting_instruction(self) -> None:
        src = "MOV A, 0\ndiv_lbl:\nDIV A\nHLT"
        result = assemble(src, arch=1)
        cpu = CPU(arch=1)
        cpu.load(result.code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.ip == result.labels["div_lbl"]

    def test_e17_deferred_vu_fault_ip_at_vwait(self) -> None:
        src = "VSET VA, 0xFF, 0xFE\nVSET VL, 0, 4\nVADD.U VC, VA, 1\nvwait_lbl:\nVWAIT\nHLT\n"
        result = assemble(src, arch=3)
        cpu = CPU(arch=3)
        cpu.load(result.code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.ip == result.labels["vwait_lbl"]

    def test_e18_no_execution_after_fault(self) -> None:
        cpu = _run_fault("MOV A, 0\nDIV A\nMOV B, 99\nHLT")
        assert cpu.b == 0

    def test_e19_a_stays_as_error_code(self) -> None:
        cpu = _run_fault("MOV A, 0\nDIV A\nADD A, 10\nHLT")
        assert cpu.a == int(ErrorCode.DIV_ZERO)


# ── E.3 Pre-Check Atomicity ──────────────────────────────────────────


class TestFaultAtomicity:
    """Spec §E.3 — faults fire before any state is modified."""

    def test_e20_push_fault_before_write(self) -> None:
        cpu = _run_fault("MOV B, 99\nMOV SP, 0\nPUSH B\nHLT")
        assert cpu.sp == 0  # SP not decremented on overflow fault
        assert cpu.mem[0] != 99  # B's value not written (code byte occupies mem[0])

    def test_e21_page_oob_no_write(self) -> None:
        cpu = _run_fault("MOV A, 250\nMOV [A+10], 42\nHLT")
        # The write at offset 260 must not have happened
        for addr in range(256, 512):
            assert cpu.mem[addr] == 0

    def test_e22_div_fault_before_quotient(self) -> None:
        cpu = _run_fault("MOV A, 5\nMOV B, 0\nDIV B\nHLT")
        # A must hold the error code, not the quotient
        assert cpu.a == int(ErrorCode.DIV_ZERO)


# ── E.4 Reserved Codes Not Produced ─────────────────────────────────


class TestReservedCodes:
    """Spec §E.4 — codes 7–11 never appear."""

    VALID_CODES = frozenset([1, 2, 3, 4, 5, 6, 12, 13, 14])

    @pytest.mark.parametrize(
        "source,arch",
        [
            pytest.param("MOV A, 0\nDIV A\nHLT", 1, id="div_zero"),
            pytest.param("MOV SP, 0\nPUSH A\nHLT", 1, id="stack_overflow"),
            pytest.param("POP A\nHLT", 1, id="stack_underflow"),
            pytest.param("DB 70, 6, 0\nHLT", 1, id="invalid_reg"),
            pytest.param("MOV B, 250\nMOV A, [B+15]", 1, id="page_boundary"),
            pytest.param("DB 9\nHLT", 1, id="invalid_opcode"),
        ],
    )
    def test_e23_code_in_valid_set(self, source: str, arch: int) -> None:
        cpu = _run_fault(source, arch=arch)
        assert cpu.a in self.VALID_CODES


# ── E.5 FP Exception vs FAULT Distinction ──────────────────────────


class TestFpExceptionVsFault:
    """Spec §E.5 — FP arithmetic exceptions set FPSR, do not FAULT."""

    def test_e24_fp_divzero_sets_fpsr_dz_not_fault(self) -> None:
        # 1.0f / 0.0f → +inf; DZ flag set; no FAULT
        src = (
            "FMOV.F FA, [one]\n"
            "FDIV.F FA, [zero]\n"
            "HLT\n"
            "one: DB 0x00,0x00,0x80,0x3F\n"  # 1.0f LE
            "zero: DB 0,0,0,0\n"
        )
        cpu = _run_fp(src)
        assert cpu.state == CpuState.HALTED
        assert cpu.fault is False
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.fpsr & FpuRegisters.FPSR_DZ

    def test_e25_fp_nan_input_sets_fpsr_nv_not_fault(self) -> None:
        # NaN + 1.0f → NaN; NV flag set; no FAULT
        src = (
            "FMOV.F FA, [nan]\n"
            "FADD.F FA, [one]\n"
            "HLT\n"
            "nan: DB 0x00,0x00,0xC0,0x7F\n"  # canonical NaN LE
            "one: DB 0x00,0x00,0x80,0x3F\n"
        )
        cpu = _run_fp(src)
        assert cpu.state == CpuState.HALTED
        assert cpu.fault is False
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.fpsr & FpuRegisters.FPSR_NV

    def test_e26_invalid_fpm_causes_fault_not_exception(self) -> None:
        cpu = CPU(arch=2)
        cpu.load([int(Op.FABS_FP), 0x07, int(Op.HLT)])
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.FP_FORMAT)


# ── E.6 VU Exception vs FAULT Distinction ───────────────────────────


class TestVuExceptionVsFault:
    """Spec §E.6 — VU FP exceptions set VFPSR; VU int faults → deferred FAULT."""

    def test_e27_vu_fp_divzero_sets_vfpsr_not_fault(self) -> None:
        # 1.0f / 0.0f: sets VFPSR.DZ, no FAULT
        src = (
            "MOV [0x40], 0\n"
            "MOV [0x41], 0\n"
            "MOV [0x42], 0x80\n"
            "MOV [0x43], 0x3F\n"  # mem[0x40..43] = 1.0f LE
            "VSET VA, 0, 0x40\n"
            "VSET VB, 0, 0x50\n"  # 0.0f (zeroed memory)
            "VSET VC, 0, 0x60\n"
            "VSET VL, 0, 1\n"
            "VDIV.F VC, VA, VB\n"
            "VWAIT\n"
            "HLT\n"
        )
        cpu, _ = _run_vu(src)
        assert cpu.state == CpuState.HALTED
        assert cpu.fault is False
        assert cpu.regs.vu is not None
        assert cpu.regs.vu.vfpsr & 0x02  # FPSR_DZ bit

    def test_e28_vu_int_divzero_deferred_fault(self) -> None:
        # 1 / 0 integer: deferred FAULT(ERR_DIV_ZERO) at VWAIT
        src = (
            "MOV [0x40], 1\n"  # VA[0] = 1
            "VSET VA, 0, 0x40\n"
            "VSET VB, 0, 0x50\n"  # VB[0] = 0
            "VSET VC, 0, 0x60\n"
            "VSET VL, 0, 1\n"
            "VDIV.U VC, VA, VB\n"
            "VWAIT\n"
            "HLT\n"
        )
        cpu, _ = _run_vu(src)
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.DIV_ZERO)

    def test_e29_vsqrt_uint_format_fault(self) -> None:
        # VSQRT with UINT8 format → ERR_VU_FORMAT
        cpu = CPU(arch=3)
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)
        code = (
            [163, 4, 1, 0]  # VSET VL, 1
            + [int(Op.VSQRT), vfm_enc, encode_vu_regs(2, 0, 0)]
            + [int(Op.VWAIT), int(Op.HLT)]
        )
        cpu.load(code)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == int(ErrorCode.VU_FORMAT)
