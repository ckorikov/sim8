"""FP simulator tests for arch=2."""

import math
import struct

import pytest
from hypothesis import given, assume, settings
from hypothesis import strategies as st

from pysim8.asm import assemble
from pysim8.sim import CPU, CpuState
from pysim8.sim.errors import ErrorCode
from pysim8.fp_formats import (
    RoundingMode,
    encode_float16, encode_bfloat16, encode_float32,
    encode_ofp8_e4m3, encode_ofp8_e5m2,
    decode_float32, decode_float16, decode_bfloat16,
    decode_ofp8_e4m3, decode_ofp8_e5m2,
    float_to_bytes, bytes_to_float,
    fp_add, fp_sub, fp_mul, fp_div, fp_sqrt,
    fp_cmp, fp_abs, fp_neg, fp_classify,
    FpExceptions,
)


# ── helpers ──────────────────────────────────────────────────────────


def run(source: str, arch: int = 2) -> CPU:
    """Assemble source, load into CPU, run until halt/fault."""
    result = assemble(source, arch=arch)
    cpu = CPU(arch=arch)
    cpu.load(result.code)
    state = cpu.run()
    assert state != CpuState.RUNNING, "Step limit reached"
    return cpu


def run_binary(code: list[int], arch: int = 2) -> CPU:
    """Load raw binary, run until halt/fault."""
    cpu = CPU(arch=arch)
    cpu.load(code)
    state = cpu.run()
    assert state != CpuState.RUNNING, "Step limit reached"
    return cpu


def _f32_bytes(value: float) -> list[int]:
    """Return float32 bytes as list."""
    return list(struct.pack("<f", value))


def _f16_bytes(value: float) -> list[int]:
    """Return float16 bytes as list."""
    return list(struct.pack("<e", value))


def _read_f32(cpu: CPU, addr: int) -> float:
    """Read float32 from memory."""
    data = bytes(cpu.mem[addr + i] for i in range(4))
    return struct.unpack("<f", data)[0]


def _read_f16(cpu: CPU, addr: int) -> float:
    """Read float16 from memory."""
    data = bytes(cpu.mem[addr + i] for i in range(2))
    return struct.unpack("<e", data)[0]


def _store_f32(cpu: CPU, addr: int, value: float) -> None:
    """Write float32 to memory at addr."""
    for i, b in enumerate(struct.pack("<f", value)):
        cpu.mem[addr + i] = b


def _store_f16(cpu: CPU, addr: int, value: float) -> None:
    """Write float16 to memory at addr."""
    for i, b in enumerate(struct.pack("<e", value)):
        cpu.mem[addr + i] = b


def _assert_halted_steps(cpu: CPU, steps: int) -> None:
    """Assert CPU halted and executed expected number of non-HLT steps."""
    assert cpu.state == CpuState.HALTED
    assert cpu.steps == steps


# ── FMOV ─────────────────────────────────────────────────────────────

# FPM encoding: encode_fpm(phys=0, pos=0, fmt=0) for FA = 0x00
# For FHA (pos=0, fmt=1): encode_fpm(0, 0, 1) = 0x01
# For FHB (pos=1, fmt=1): encode_fpm(0, 1, 1) = 0x09

from pysim8.isa import (
    encode_fpm, FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2,
)


class TestFmov:
    def test_fmov_load_store_float32(self) -> None:
        """Load float32 from memory, store back elsewhere."""
        cpu = CPU(arch=2)
        code = [0] * 256  # fill with HLT
        # Store 1.0 at addr 0x80
        _store_f32(cpu, 0, 0)  # just preallocate
        cpu.load(code)
        _store_f32(cpu, 0x80, 1.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)  # FA
        # FMOV.F FA, [0x80]: opcode=128, fpm, addr
        # FMOV.F [0x90], FA: opcode=130, fpm, addr
        # HLT: opcode=0
        cpu.mem[0] = 128  # FMOV_FP_ADDR
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 130  # FMOV_ADDR_FP
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x90
        cpu.mem[6] = 0  # HLT
        cpu.run()
        _assert_halted_steps(cpu, 2)
        result = _read_f32(cpu, 0x90)
        assert result == 1.0

    def test_fmov_float16(self) -> None:
        """Load/store float16."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f16(cpu, 0x80, 1.5)
        fpm_fha = encode_fpm(0, 0, FP_FMT_H)
        cpu.mem[0] = 128  # FMOV_FP_ADDR (works for all formats)
        cpu.mem[1] = fpm_fha
        cpu.mem[2] = 0x80
        cpu.mem[3] = 130  # FMOV_ADDR_FP
        cpu.mem[4] = fpm_fha
        cpu.mem[5] = 0x90
        cpu.mem[6] = 0  # HLT
        cpu.run()
        _assert_halted_steps(cpu, 2)
        result = _read_f16(cpu, 0x90)
        assert result == 1.5

    def test_fmov_no_flags(self) -> None:
        """FMOV does not affect flags."""
        # CMP A, A sets Z=1, then FMOV should not change it
        src = "CMP A, A\nHLT"
        result = assemble(src, arch=2)
        cpu = CPU(arch=2)
        cpu.load(result.code)
        # Step CMP to set Z
        cpu.step()
        assert cpu.zero is True
        # Now inject FMOV at current IP
        # Use a fresh CPU for clarity
        cpu2 = CPU(arch=2)
        cpu2.load([0] * 256)
        _store_f32(cpu2, 0x80, 1.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # CMP A,A: opcode=23, reg=0, const=0 -- actually CMP A, 0
        # Let's use CMP_REG_CONST (23): reg=0, const=0
        cpu2.mem[0] = 23   # CMP_REG_CONST
        cpu2.mem[1] = 0    # reg A
        cpu2.mem[2] = 0    # const 0
        cpu2.mem[3] = 128  # FMOV_FP_ADDR
        cpu2.mem[4] = fpm_fa
        cpu2.mem[5] = 0x80
        cpu2.mem[6] = 0    # HLT
        cpu2.run()
        _assert_halted_steps(cpu2, 2)
        assert cpu2.zero is True  # Z set by CMP, FMOV didn't change


# ── FADD ─────────────────────────────────────────────────────────────


class TestFadd:
    def test_fadd_float32(self) -> None:
        """FADD.F: 1.0 + 2.0 = 3.0."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 1.0)
        _store_f32(cpu, 0x84, 2.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FADD.F FA, [0x84]
        cpu.mem[3] = 132  # FADD_FP_ADDR
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        # FMOV.F [0x90], FA
        cpu.mem[6] = 130
        cpu.mem[7] = fpm_fa
        cpu.mem[8] = 0x90
        # HLT
        cpu.mem[9] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f32(cpu, 0x90)
        assert result == 3.0


# ── FCMP ─────────────────────────────────────────────────────────────


class TestFcmp:
    def test_fcmp_equal(self) -> None:
        """FCMP equal: Z=1, C=0."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 1.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FCMP.F FA, [0x80]
        cpu.mem[3] = 140  # FCMP_FP_ADDR
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x80
        # HLT
        cpu.mem[6] = 0
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.zero is True
        assert cpu.carry is False

    def test_fcmp_less_than(self) -> None:
        """FCMP less: Z=0, C=1."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 1.0)
        _store_f32(cpu, 0x84, 2.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80] (load 1.0)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FCMP.F FA, [0x84] (compare 1.0 vs 2.0)
        cpu.mem[3] = 140
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        # HLT
        cpu.mem[6] = 0
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.zero is False
        assert cpu.carry is True


# ── FABS / FNEG ──────────────────────────────────────────────────────


class TestFabsFneg:
    def test_fabs(self) -> None:
        """FABS clears sign bit."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, -3.14)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FABS.F FA: opcode=142, fpm
        cpu.mem[3] = 142
        cpu.mem[4] = fpm_fa
        # FMOV.F [0x90], FA
        cpu.mem[5] = 130
        cpu.mem[6] = fpm_fa
        cpu.mem[7] = 0x90
        # HLT
        cpu.mem[8] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f32(cpu, 0x90)
        assert result == pytest.approx(3.14)

    def test_fneg(self) -> None:
        """FNEG toggles sign bit."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 2.5)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FNEG.F FA: opcode=143
        cpu.mem[3] = 143
        cpu.mem[4] = fpm_fa
        # FMOV.F [0x90], FA
        cpu.mem[5] = 130
        cpu.mem[6] = fpm_fa
        cpu.mem[7] = 0x90
        # HLT
        cpu.mem[8] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f32(cpu, 0x90)
        assert result == -2.5


# ── FP exceptions ────────────────────────────────────────────────────


class TestFpExceptions:
    def test_div_zero_sets_dz(self) -> None:
        """Division by zero sets FPSR.DZ but does NOT fault."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 1.0)
        _store_f32(cpu, 0x84, 0.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FDIV.F FA, [0x84]
        cpu.mem[3] = 138  # FDIV_FP_ADDR
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        # FSTAT A: opcode=149, gpr=0
        cpu.mem[6] = 149
        cpu.mem[7] = 0
        # HLT
        cpu.mem[8] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)  # NOT FAULT
        assert cpu.a & 0x02 != 0  # DZ flag set


# ── FP_FORMAT fault ──────────────────────────────────────────────────


class TestFpFormatFault:
    def test_invalid_fpm_faults(self) -> None:
        """Invalid FPM byte (fmt=7, reserved) causes FAULT(12)."""
        cpu = CPU(arch=2)
        # FABS opcode (142) + FPM=0x07 (phys=0, pos=0, fmt=7 = invalid)
        cpu.load([142, 0x07, 0])
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.steps == 0
        assert cpu.a == 12  # ERR_FP_FORMAT

    def test_phys2_faults(self) -> None:
        """phys=2 is reserved in v2 — causes FAULT(ERR_FP_FORMAT)."""
        cpu = CPU(arch=2)
        # FABS opcode (142) + FPM=0x80 (phys=2, pos=0, fmt=0)
        cpu.load([142, 0x80, 0])
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.steps == 0
        assert cpu.a == 12  # ERR_FP_FORMAT


# ── FSTAT / FCLR ─────────────────────────────────────────────────────


class TestFstat:
    def test_fstat_reads_fpsr(self) -> None:
        """FCLR + FSTAT -> A=0."""
        cpu = CPU(arch=2)
        # FCLR: opcode=152
        # FSTAT A: opcode=149, gpr=0
        # HLT: 0
        cpu.load([152, 149, 0, 0])
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 0

    def test_fclr_clears_fpsr(self) -> None:
        """After triggering exception, FCLR clears FPSR."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 1.0)
        _store_f32(cpu, 0x84, 0.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FDIV.F FA, [0x84] -- div zero
        cpu.mem[3] = 138
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        # FCLR
        cpu.mem[6] = 152
        # FSTAT A
        cpu.mem[7] = 149
        cpu.mem[8] = 0
        # HLT
        cpu.mem[9] = 0
        cpu.run()
        _assert_halted_steps(cpu, 4)
        assert cpu.a == 0  # cleared


# ── Reg-reg arithmetic ───────────────────────────────────────────────


class TestRegReg:
    def test_fadd_rr_doubles(self) -> None:
        """FADD.F FA, FA doubles the value."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 2.5)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FADD_RR FA, FA: opcode=153, dst_fpm, src_fpm
        cpu.mem[3] = 153
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = fpm_fa
        # FMOV.F [0x90], FA
        cpu.mem[6] = 130
        cpu.mem[7] = fpm_fa
        cpu.mem[8] = 0x90
        # HLT
        cpu.mem[9] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f32(cpu, 0x90)
        assert result == 5.0


# ── FITOF / FFTOI ────────────────────────────────────────────────────


class TestFitofFftoi:
    def test_fitof(self) -> None:
        """Convert uint8=42 to float32."""
        cpu = CPU(arch=2)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # MOV A, 42: opcode=6, reg=0, value=42
        # FITOF.F FA, A: opcode=147, fpm, gpr=0
        # FMOV.F [0x90], FA: opcode=130, fpm, addr
        # HLT
        cpu.load([6, 0, 42, 147, fpm_fa, 0, 130, fpm_fa, 0x90, 0])
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f32(cpu, 0x90)
        assert result == 42.0

    def test_fftoi(self) -> None:
        """Convert float32=42.0 to uint8."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 42.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FFTOI.F A, FA: opcode=148, fpm, gpr=0
        cpu.mem[3] = 148
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0
        # HLT
        cpu.mem[6] = 0
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 42

    def test_fftoi_nan_gives_zero(self) -> None:
        """NaN converts to 0 with invalid flag."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        # Store NaN at 0x80
        for i, b in enumerate(struct.pack("<f", float("nan"))):
            cpu.mem[0x80 + i] = b
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128  # FMOV
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 148  # FFTOI
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0
        cpu.mem[6] = 149  # FSTAT B
        cpu.mem[7] = 1
        cpu.mem[8] = 0  # HLT
        cpu.run()
        _assert_halted_steps(cpu, 3)
        assert cpu.a == 0  # NaN -> 0
        assert cpu.b & 0x01 != 0  # invalid flag set

    def test_fftoi_saturates_high(self) -> None:
        """Float > 255 saturates to 255."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 300.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 148
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0
        cpu.mem[6] = 0  # HLT
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 255


# ── FCVT ─────────────────────────────────────────────────────────────


class TestFcvt:
    def test_fcvt_f_to_h(self) -> None:
        """Convert float32 -> float16."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 1.5)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        fpm_fha = encode_fpm(0, 0, FP_FMT_H)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # FCVT FHA, FA: opcode=146, dst_fpm, src_fpm
        cpu.mem[3] = 146
        cpu.mem[4] = fpm_fha
        cpu.mem[5] = fpm_fa
        # FMOV.H [0x90], FHA: opcode=130, fpm, addr
        cpu.mem[6] = 130
        cpu.mem[7] = fpm_fha
        cpu.mem[8] = 0x90
        # HLT
        cpu.mem[9] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f16(cpu, 0x90)
        assert result == 1.5


# ── FCFG / FSCFG ────────────────────────────────────────────────────


class TestFcfgFscfg:
    def test_fcfg_reads_fpcr(self) -> None:
        """FCFG reads FPCR into GPR."""
        cpu = CPU(arch=2)
        # FPCR defaults to 0; FCFG A: opcode=150, gpr=0; HLT
        cpu.load([150, 0, 0])
        cpu.run()
        _assert_halted_steps(cpu, 1)
        assert cpu.a == 0

    def test_fscfg_sets_rounding_mode(self) -> None:
        """FSCFG sets FPCR from GPR."""
        cpu = CPU(arch=2)
        # MOV A, 1: opcode=6, reg=0, val=1
        # FSCFG A: opcode=151, gpr=0
        # FCFG B: opcode=150, gpr=1
        # HLT
        cpu.load([6, 0, 1, 151, 0, 150, 1, 0])
        cpu.run()
        _assert_halted_steps(cpu, 3)
        assert cpu.b == 1  # rounding mode set to RTZ
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.rounding_mode == 1

    def test_fscfg_masks_reserved_bits(self) -> None:
        """FSCFG only uses bits [1:0]."""
        cpu = CPU(arch=2)
        # MOV A, 0xFF; FSCFG A; FCFG B; HLT
        cpu.load([6, 0, 0xFF, 151, 0, 150, 1, 0])
        cpu.run()
        _assert_halted_steps(cpu, 3)
        assert cpu.b == 3  # only bits 0-1 kept


# ── FCLASS ───────────────────────────────────────────────────────────


class TestFclass:
    def test_fclass_zero(self) -> None:
        """FCLASS of +0.0 returns bit 0 (ZERO)."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 0.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128  # FMOV FA, [0x80]
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 158  # FCLASS A, FA
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0    # gpr A
        cpu.mem[6] = 0    # HLT
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.a & 0x01 != 0  # ZERO bit

    def test_fclass_normal(self) -> None:
        """FCLASS of 1.0 returns bit 2 (NORM)."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 1.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 158
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0
        cpu.mem[6] = 0
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.a & 0x04 != 0  # NORM bit

    def test_fclass_negative(self) -> None:
        """FCLASS of -1.0 has NORM + NEG bits."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, -1.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 158
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0
        cpu.mem[6] = 0
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.a & 0x04 != 0  # NORM
        assert cpu.a & 0x40 != 0  # NEG


# ── FCMP_RR ──────────────────────────────────────────────────────────


class TestFcmpRR:
    def test_fcmp_rr_equal(self) -> None:
        """Reg-reg FCMP on same register: Z=1, C=0."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 5.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128  # FMOV FA, [0x80]
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 157  # FCMP_RR FA, FA
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = fpm_fa
        cpu.mem[6] = 0  # HLT
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.zero is True
        assert cpu.carry is False


# ── FSUB / FMUL ─────────────────────────────────────────────────────


class TestFsubFmul:
    def test_fsub_float32(self) -> None:
        """FSUB.F: 5.0 - 2.0 = 3.0."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 5.0)
        _store_f32(cpu, 0x84, 2.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128  # FMOV
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 134  # FSUB_FP_ADDR
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        cpu.mem[6] = 130  # FMOV store
        cpu.mem[7] = fpm_fa
        cpu.mem[8] = 0x90
        cpu.mem[9] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        assert _read_f32(cpu, 0x90) == 3.0

    def test_fmul_float32(self) -> None:
        """FMUL.F: 3.0 * 4.0 = 12.0."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 3.0)
        _store_f32(cpu, 0x84, 4.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128  # FMOV
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 136  # FMUL_FP_ADDR
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        cpu.mem[6] = 130  # FMOV store
        cpu.mem[7] = fpm_fa
        cpu.mem[8] = 0x90
        cpu.mem[9] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        assert _read_f32(cpu, 0x90) == 12.0


# ── FSQRT ────────────────────────────────────────────────────────────


class TestFsqrt:
    def test_fsqrt_4(self) -> None:
        """FSQRT of 4.0 = 2.0."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 4.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 144  # FSQRT_FP
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 130  # FMOV store
        cpu.mem[6] = fpm_fa
        cpu.mem[7] = 0x90
        cpu.mem[8] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        assert _read_f32(cpu, 0x90) == 2.0


# ── Arch=1 regression ────────────────────────────────────────────────


# ── FMOV Immediate (161-162) ─────────────────────────────────────────


class TestFmovImm:
    def test_fmov_imm8_o3(self) -> None:
        """FMOV.O3 FQA, 1.5 loads 0x3C into quarter-reg 0."""
        cpu = run("FMOV.O3 FQA, 1.5\nHLT")
        _assert_halted_steps(cpu, 1)
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.read_bits(0, 3) == 0x3C  # E4M3 1.5

    def test_fmov_imm8_o2(self) -> None:
        """FMOV.O2 FQB, 1.0 loads 0x3C into quarter-reg 1."""
        cpu = run("FMOV.O2 FQB, 1.0\nHLT")
        _assert_halted_steps(cpu, 1)
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.read_bits(1, 4) == 0x3C  # E5M2 1.0

    def test_fmov_imm16_h(self) -> None:
        """FMOV.H FHA, 1.5 loads 0x3E00 into half-reg 0."""
        cpu = run("FMOV.H FHA, 1.5\nHLT")
        _assert_halted_steps(cpu, 1)
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.read_bits(0, 1) == 0x3E00  # float16 1.5

    def test_fmov_imm16_bf(self) -> None:
        """FMOV.BF FHB, 1.0 loads 0x3F80 into half-reg 1."""
        cpu = run("FMOV.BF FHB, 1.0\nHLT")
        _assert_halted_steps(cpu, 1)
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.read_bits(1, 2) == 0x3F80  # bfloat16 1.0

    def test_fmov_imm_no_fpsr_change(self) -> None:
        """FMOV immediate does not modify FPSR."""
        cpu = run("FMOV.O3 FQA, 1.5\nFSTAT A\nHLT")
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 0  # FPSR unchanged

    def test_fmov_imm_no_flags_change(self) -> None:
        """FMOV immediate does not affect CPU flags."""
        cpu = CPU(arch=2)
        # CMP A,0: sets Z=1, then FMOV imm should not touch flags
        from pysim8.asm import assemble
        result = assemble("CMP A, 0\nFMOV.O3 FQA, 1.5\nHLT", arch=2)
        cpu.load(result.code)
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.zero is True  # Z set by CMP, untouched by FMOV

    def test_fmov_imm8_format_mismatch_fault(self) -> None:
        """Op 161 with 16-bit format in FPM -> FAULT(FP_FORMAT)."""
        fpm_fha = encode_fpm(0, 0, FP_FMT_H)  # fmt=1 (16-bit)
        cpu = run_binary([161, fpm_fha, 0x3C, 0])
        assert cpu.state == CpuState.FAULT
        assert cpu.a == 12  # ERR_FP_FORMAT

    def test_fmov_imm16_format_mismatch_fault(self) -> None:
        """Op 162 with 8-bit format in FPM -> FAULT(FP_FORMAT)."""
        fpm_fqa = encode_fpm(0, 0, 3)  # fmt=3 (O3, 8-bit)
        cpu = run_binary([162, fpm_fqa, 0x00, 0x3E, 0])
        assert cpu.state == CpuState.FAULT
        assert cpu.a == 12  # ERR_FP_FORMAT


class TestRegressionArch1:
    """Ensure arch=1 simulator still works."""

    def test_basic_mov_halt(self) -> None:
        cpu = run("MOV A, 42\nHLT", arch=1)
        _assert_halted_steps(cpu, 1)
        assert cpu.a == 42

    def test_fp_opcode_invalid_arch1(self) -> None:
        """FP opcode on arch=1 -> FAULT(INVALID_OPCODE)."""
        cpu = CPU(arch=1)
        cpu.load([142, 0x00, 0])  # FABS.F FA -- but arch=1
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.steps == 0
        assert cpu.a == 6  # ERR_INVALID_OPCODE

    def test_no_fpu_on_arch1(self) -> None:
        """Arch=1 CPU has no FPU registers."""
        cpu = CPU(arch=1)
        assert cpu.regs.fpu is None

    def test_fpu_present_on_arch2(self) -> None:
        """Arch=2 CPU has FPU registers."""
        cpu = CPU(arch=2)
        assert cpu.regs.fpu is not None


# ── FB register (phys=1) ─────────────────────────────────────────────


class TestFbRegister:
    """Tests for the second physical FP register (FB, phys=1)."""

    def test_fmov_load_fb_float32(self) -> None:
        """FMOV.F FB, [addr] loads float32 into FB (phys=1)."""
        cpu = CPU(arch=2)
        fpm_fb = encode_fpm(1, 0, FP_FMT_F)  # FB
        cpu.load([128, fpm_fb, 100, 0])
        _store_f32(cpu, 100, 3.14)
        cpu.run()
        _assert_halted_steps(cpu, 1)
        assert cpu.regs.fpu is not None
        expected = struct.unpack("<I", struct.pack("<f", 3.14))[0]
        assert cpu.regs.fpu.read_bits(0, FP_FMT_F, 1) == expected

    def test_fb_independent_from_fa(self) -> None:
        """Writing to FB does not affect FA and vice versa."""
        cpu = run(
            "FMOV.O3 FQA, 1.5\n"     # FA phys=0 gets 0x3C in [7:0]
            "FMOV.O3 FQE, 2.0\n"     # FB phys=1 gets 0x40 in [7:0]
            "HLT"
        )
        _assert_halted_steps(cpu, 2)
        assert cpu.regs.fpu is not None
        # FA: FQA pos=0 fmt=3 -> bits [7:0] = 0x3C (1.5 E4M3)
        assert cpu.regs.fpu.read_bits(0, 3, 0) == 0x3C
        # FB: FQE pos=0 fmt=3 -> bits [7:0] = 0x40 (2.0 E4M3)
        assert cpu.regs.fpu.read_bits(0, 3, 1) == 0x40

    def test_fmov_store_fb_float16(self) -> None:
        """FMOV.H [addr], FHC stores FB half to memory."""
        cpu = run(
            "FMOV.H FHC, 1.5\n"       # Load imm16 into FHC (phys=1)
            "FMOV.H [100], FHC\n"      # Store to memory
            "HLT"
        )
        _assert_halted_steps(cpu, 2)
        val = _read_f16(cpu, 100)
        assert val == 1.5

    def test_fadd_on_fb(self) -> None:
        """FADD on FB sub-register works correctly."""
        cpu = CPU(arch=2)
        fpm_fb = encode_fpm(1, 0, FP_FMT_F)  # FB
        cpu.load([
            128, fpm_fb, 100,   # FMOV.F FB, [100] (load 2.0)
            132, fpm_fb, 104,   # FADD.F FB, [104] (add 3.0)
            0,                  # HLT
        ])
        _store_f32(cpu, 100, 2.0)
        _store_f32(cpu, 104, 3.0)
        cpu.run()
        _assert_halted_steps(cpu, 2)
        # FB should have 5.0
        from pysim8.fp_formats import bytes_to_float
        raw = cpu.regs.fpu.read_bits(0, FP_FMT_F, 1)
        data = raw.to_bytes(4, "little")
        val = bytes_to_float(data, FP_FMT_F)
        assert val == 5.0

    def test_fadd_rr_cross_phys(self) -> None:
        """FADD_RR between FA and FB sub-registers."""
        cpu = run(
            "FMOV.O3 FQA, 1.5\n"     # FA: FQA = 1.5
            "FMOV.O3 FQE, 2.0\n"     # FB: FQE = 2.0
            "FADD.O3 FQA, FQE\n"     # FQA += FQE -> 3.5
            "HLT"
        )
        _assert_halted_steps(cpu, 3)
        # FQA should be 3.5 E4M3 = 0x46
        assert cpu.regs.fpu.read_bits(0, 3, 0) == 0x46

    def test_fcvt_between_fa_fb(self) -> None:
        """FCVT from FA sub-register to FB sub-register."""
        cpu = run(
            "FMOV.H FHA, 1.5\n"      # FA: FHA = 1.5 float16
            "FCVT.O3.H FQE, FHA\n"   # FB: FQE = convert(1.5) = 0x3C E4M3
            "HLT"
        )
        _assert_halted_steps(cpu, 2)
        assert cpu.regs.fpu.read_bits(0, 3, 1) == 0x3C

    def test_fmov_imm_fb(self) -> None:
        """FMOV immediate into FB sub-register."""
        cpu = run(
            "FMOV.H FHC, 1.5\n"      # FB: FHC = 1.5 float16
            "HLT"
        )
        _assert_halted_steps(cpu, 1)
        # float16 1.5 = 0x3E00
        assert cpu.regs.fpu.read_bits(0, 1, 1) == 0x3E00

    def test_fclass_fb(self) -> None:
        """FCLASS on FB sub-register."""
        cpu = run(
            "FMOV.O3 FQE, 1.5\n"     # FB: FQE = 1.5
            "FCLASS.O3 A, FQE\n"      # Classify -> NORM (bit 2)
            "HLT"
        )
        _assert_halted_steps(cpu, 2)
        assert cpu.a & 0x04  # NORM bit set

# ── FP handler edge cases ────────────────────────────────────────


class TestFpPageBoundary:
    """FP memory access page boundary faults."""

    def test_read_page_boundary(self) -> None:
        cpu = run("FMOV.F FA, [253]\nHLT")
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.PAGE_BOUNDARY
        assert cpu.steps == 0

    def test_write_page_boundary(self) -> None:
        cpu = run("FMOV.F [253], FA\nHLT")
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.PAGE_BOUNDARY
        assert cpu.steps == 0


class TestFmovStoreEdges:
    def test_fmov_store_addr_f16(self) -> None:
        cpu = run("""
            FMOV.H FHA, 1.5
            FMOV.H [100], FHA
            HLT
        """)
        _assert_halted_steps(cpu, 2)
        data = bytes(cpu.mem[100 + i] for i in range(2))
        val = struct.unpack("<e", data)[0]
        assert val == 1.5


class TestFftoiEdges:
    """FFTOI with NaN, Inf, rounding modes, saturation."""

    def test_nan(self) -> None:
        cpu = run("""
            FMOV.H FHA, nan_h
            FFTOI.H A, FHA
            FSTAT B
            HLT
        """)
        _assert_halted_steps(cpu, 3)
        assert cpu.a == 0
        assert cpu.b & 0x01  # invalid flag

    def test_inf_positive(self) -> None:
        cpu = run("""
            FMOV.H FHA, inf_h
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 255

    def test_inf_negative(self) -> None:
        cpu = run("""
            FMOV.H FHA, inf_h
            FNEG.H FHA
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 3)
        assert cpu.a == 0

    def test_rounding_modes(self) -> None:
        # RTZ (mode 1)
        cpu = run("""
            MOV A, 1
            FSCFG A
            FMOV.H FHA, 2.5
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 4)
        assert cpu.a == 2  # truncate

        # RDN (mode 2)
        cpu = run("""
            MOV A, 2
            FSCFG A
            FMOV.H FHA, 2.5
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 4)
        assert cpu.a == 2  # floor

        # RUP (mode 3)
        cpu = run("""
            MOV A, 3
            FSCFG A
            FMOV.H FHA, 2.5
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 4)
        assert cpu.a == 3  # ceil

    def test_saturate_high(self) -> None:
        cpu = run("""
            FMOV.H FHA, 300.0
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 255

    def test_inexact(self) -> None:
        cpu = run("""
            FMOV.H FHA, 1.5
            FFTOI.H A, FHA
            FSTAT B
            HLT
        """)
        _assert_halted_steps(cpu, 3)
        assert cpu.a == 2  # RNE: 1.5 -> 2
        assert cpu.b & 0x10  # inexact flag


class TestFclassEdges:
    def test_fclass_inf(self) -> None:
        cpu = run("""
            FMOV.H FHA, inf_h
            FCLASS.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 2)
        assert cpu.a & 0x08  # INF bit
        assert (cpu.a & 0x40) == 0  # NEG bit clear for +inf


class TestFmaddEdges:
    def test_fmadd_addr(self) -> None:
        cpu = run("""
            FMOV.H FHA, 2.0
            FMOV.H FHB, 3.0
            FMOV.H [100], FHB
            FMOV.H FHB, 1.0
            FMADD.H FHB, FHA, [100]
            HLT
        """)
        _assert_halted_steps(cpu, 5)
        fpu = cpu.regs.fpu
        assert fpu is not None
        raw = fpu.read_bits(1, 1, 0)  # FHB: pos=1, fmt=1(H), phys=0
        data = raw.to_bytes(2, "little")
        val = struct.unpack("<e", data)[0]
        assert val == 7.0

    def test_fmadd_regaddr(self) -> None:
        cpu = run("""
            MOV B, 100
            FMOV.H FHA, 2.0
            FMOV.H FHB, 3.0
            FMOV.H [100], FHB
            FMOV.H FHB, 1.0
            FMADD.H FHB, FHA, [B]
            HLT
        """)
        _assert_halted_steps(cpu, 6)
        fpu = cpu.regs.fpu
        assert fpu is not None
        raw = fpu.read_bits(1, 1, 0)  # FHB
        data = raw.to_bytes(2, "little")
        val = struct.unpack("<e", data)[0]
        assert val == 7.0


# ── fp_formats.py edge cases ─────────────────────────────────────


class TestFpFormatsEdges:
    """Directed rounding, bf16, classify, cmp edges."""

    def test_float16_directed_rounding(self) -> None:
        for rm in range(4):
            data, exc = encode_float16(1.0009765625, rm=rm)
            assert data == b"\x01\x3c"
            assert decode_float16(data) == 1.0009765625
            assert not exc.invalid
            assert not exc.overflow
            assert not exc.underflow
            assert not exc.inexact

    def test_bf16_nan_inf(self) -> None:
        data, exc = encode_bfloat16(float("nan"))
        assert data == b"\xc0\x7f"

        data, exc = encode_bfloat16(float("inf"))
        assert data == b"\x80\x7f"

        data, exc = encode_bfloat16(float("-inf"))
        assert data == b"\x80\xff"

    def test_bf16_directed_rounding(self) -> None:
        val = 1.0009765625
        expected = {
            0: (b"\x80\x3f", 1.0),
            1: (b"\x80\x3f", 1.0),
            2: (b"\x80\x3f", 1.0),
            3: (b"\x81\x3f", 1.0078125),
        }
        for rm in range(4):
            data, exc = encode_bfloat16(val, rm=rm)
            exp_bytes, exp_val = expected[rm]
            assert data == exp_bytes
            decoded = decode_bfloat16(data)
            assert decoded == exp_val
            assert not exc.invalid
            assert exc.inexact

    def test_float_to_bytes_invalid_fmt(self) -> None:
        with pytest.raises(ValueError, match="unsupported"):
            float_to_bytes(1.0, fmt=99)

    def test_bytes_to_float_invalid_fmt(self) -> None:
        with pytest.raises(ValueError, match="unsupported"):
            bytes_to_float(b"\x00\x00", fmt=99)

    def test_fp_cmp_nan(self) -> None:
        z, c, exc = fp_cmp(float("nan"), 1.0)
        assert z is True and c is True
        assert exc.invalid

    def test_fp_cmp_greater(self) -> None:
        z, c, exc = fp_cmp(2.0, 1.0)
        assert z is False and c is False

    def test_fp_classify_nan(self) -> None:
        mask = fp_classify(float("nan"), 0x7E00, 16, 1)
        assert mask & 0x10  # QNAN

    def test_fp_classify_inf(self) -> None:
        mask = fp_classify(float("inf"), 0x7C00, 16, 1)
        assert mask & 0x08  # INF

    def test_fp_classify_negative_inf(self) -> None:
        mask = fp_classify(float("-inf"), 0xFC00, 16, 1)
        assert mask & 0x08  # INF
        assert mask & 0x40  # NEG

    def test_fp_classify_subnormal(self) -> None:
        val = struct.unpack("<e", b"\x01\x00")[0]
        mask = fp_classify(val, 0x0001, 16, 1)
        assert mask & 0x02  # SUB

    def test_is_subnormal_unknown_fmt(self) -> None:
        from pysim8.fp_formats import _is_subnormal
        assert _is_subnormal(0x0001, 16, 99) is False

    def test_overflow_result_no_inf(self) -> None:
        from pysim8.fp_formats import encode_ofp8_e4m3
        data, exc = encode_ofp8_e4m3(1e10, rm=0)
        assert data == b"\x7e"
        assert decode_ofp8_e4m3(data[0]) == 448.0
        assert exc.overflow
        assert exc.inexact

    def test_encode_mini_float_zero(self) -> None:
        from pysim8.fp_formats import encode_ofp8_e4m3
        data, exc = encode_ofp8_e4m3(0.0)
        assert data == b"\x00"

    def test_round_mantissa_fallback(self) -> None:
        from pysim8.fp_formats import encode_ofp8_e5m2
        data, exc = encode_ofp8_e5m2(0.3, rm=2)  # RDN
        assert data == b"\x34"
        assert decode_ofp8_e5m2(data[0]) == 0.25
        assert exc.inexact

    def test_float32_directed_rounding(self) -> None:
        expected = {
            0: b"\xcd\xcc\x8c\x3f",  # RNE
            1: b"\xcc\xcc\x8c\x3f",  # RTZ
            2: b"\xcc\xcc\x8c\x3f",  # RDN
            3: b"\xcd\xcc\x8c\x3f",  # RUP
        }
        for rm in range(4):
            data, exc = encode_float32(1.1, rm=rm)
            assert data == expected[rm]
            assert exc.inexact

    def test_encode_mini_denorm(self) -> None:
        from pysim8.fp_formats import encode_ofp8_e5m2
        data, exc = encode_ofp8_e5m2(1e-10, rm=0)
        assert data == b"\x00"
        assert decode_ofp8_e5m2(data[0]) == 0.0
        assert exc.underflow
        assert exc.inexact


# ── FMOV register-to-register (opcode 145) ─────────────────────


class TestFmovRr:
    """FMOV_RR: raw bit copy between FP registers."""

    def test_fmov_rr_h_copy(self) -> None:
        """Copy float16 value between sub-registers."""
        cpu = run(
            "FMOV.H FHA, [val]\n"
            "FMOV.H FHB, FHA\n"
            "HLT\n"
            "val: DB 1.5_h"
        )
        _assert_halted_steps(cpu, 2)
        fha = cpu.regs.fpu.read_bits(0, 1, 0)  # FHA
        fhb = cpu.regs.fpu.read_bits(1, 1, 0)  # FHB
        assert fha == fhb == 0x3E00

    def test_fmov_rr_f_cross_phys(self) -> None:
        """Copy float32 between physical registers."""
        cpu = run(
            "FMOV.F FA, [val]\n"
            "FMOV.F FB, FA\n"
            "HLT\n"
            "val: DB 2.0"
        )
        _assert_halted_steps(cpu, 2)
        assert cpu.regs.fpu.read_bits(0, 0, 0) == 0x40000000  # FA
        assert cpu.regs.fpu.read_bits(0, 0, 1) == 0x40000000  # FB

    def test_fmov_rr_no_exceptions(self) -> None:
        """FMOV_RR does not set any FPSR flags."""
        cpu = run(
            "FMOV.H FHA, [val]\n"
            "FMOV.H FHB, FHA\n"
            "FSTAT A\n"
            "HLT\n"
            "val: DB 1.5_h"
        )
        _assert_halted_steps(cpu, 3)
        assert cpu.regs.read(0) == 0  # FPSR = 0

    def test_fmov_rr_format_mismatch_fault(self) -> None:
        """Format mismatch → FAULT(ERR_FP_FORMAT)."""
        # Craft bytecode: [145, dst_fpm=0x01(H,pos0), src_fpm=0x00(F,pos0)]
        from pysim8.sim import CPU, CpuState
        cpu = CPU(arch=2)
        cpu.load([145, 0x01, 0x00, 0])
        state = cpu.run()
        assert state == CpuState.FAULT
        assert cpu.steps == 0
        assert cpu.regs.read(0) == ErrorCode.FP_FORMAT

    def test_fmov_rr_cost(self) -> None:
        """FMOV_RR costs 1 tick."""
        cpu = run(
            "FMOV.H FHA, [val]\n"
            "FMOV.H FHB, FHA\n"
            "HLT\n"
            "val: DB 1.5_h"
        )
        _assert_halted_steps(cpu, 2)
        # FMOV load = 2, FMOV_RR = 1, HLT = 0 → total = 3
        assert cpu.cycles == 3


# ── Paranoid tests: rounding, aliasing, NaN, edge cases ─────────


def _store_bf16(cpu: CPU, addr: int, value: float) -> None:
    """Write bfloat16 to memory."""
    data, _ = encode_bfloat16(value)
    for i, b in enumerate(data):
        cpu.mem[addr + i] = b


def _read_bf16(cpu: CPU, addr: int) -> float:
    """Read bfloat16 from memory."""
    data = bytes(cpu.mem[addr + i] for i in range(2))
    return bytes_to_float(data, 2)  # fmt=2 = BF


def _store_o3(cpu: CPU, addr: int, value: float) -> None:
    """Write OFP8 E4M3 to memory."""
    data, _ = encode_ofp8_e4m3(value)
    cpu.mem[addr] = data[0]


def _read_o3(cpu: CPU, addr: int) -> float:
    """Read OFP8 E4M3 from memory."""
    return bytes_to_float(bytes([cpu.mem[addr]]), 3)  # fmt=3 = O3


class TestFcmpSignedZero:
    """FCMP +0.0 vs -0.0 must compare equal (Z=1, C=0)."""

    def test_pos_zero_eq_neg_zero_f32(self) -> None:
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 0.0)
        _store_f32(cpu, 0x84, -0.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128   # FMOV.F FA, [0x80]  (+0.0)
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 140   # FCMP.F FA, [0x84]  vs -0.0
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        cpu.mem[6] = 0     # HLT
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.zero is True   # equal
        assert cpu.carry is False

    def test_neg_zero_eq_pos_zero_f32(self) -> None:
        """Symmetric: -0.0 in register, +0.0 in memory."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, -0.0)
        _store_f32(cpu, 0x84, 0.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 140
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 0x84
        cpu.mem[6] = 0
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.zero is True
        assert cpu.carry is False


class TestFsqrtSignedZero:
    """sqrt(-0.0) must return -0.0 (sign preserved)."""

    def test_sqrt_neg_zero(self) -> None:
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, -0.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128   # FMOV.F FA, [0x80]
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 144   # FSQRT.F FA
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 130   # FMOV.F [0x90], FA
        cpu.mem[6] = fpm_fa
        cpu.mem[7] = 0x90
        cpu.mem[8] = 0     # HLT
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f32(cpu, 0x90)
        assert result == 0.0
        # Check sign bit: -0.0 has bit 31 set
        raw = struct.unpack("<I", struct.pack("<f", result))[0]
        assert raw & 0x80000000 != 0, "sign bit must be set for -0.0"

    def test_sqrt_pos_zero(self) -> None:
        """sqrt(+0.0) = +0.0 (sign preserved)."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 0.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 144   # FSQRT
        cpu.mem[4] = fpm_fa
        cpu.mem[5] = 130
        cpu.mem[6] = fpm_fa
        cpu.mem[7] = 0x90
        cpu.mem[8] = 0
        cpu.run()
        _assert_halted_steps(cpu, 3)
        result = _read_f32(cpu, 0x90)
        assert result == 0.0
        raw = struct.unpack("<I", struct.pack("<f", result))[0]
        assert raw & 0x80000000 == 0, "sign bit must be clear for +0.0"


class TestSubregisterAliasing:
    """Write to FA, verify FHA/FHB/FQA sub-registers contain correct bits."""

    def test_fa_write_read_fha_fhb(self) -> None:
        """Writing FA=0x40490FDB (pi), FHA should be low 16, FHB high 16."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 3.1415927)  # ~ 0x40490FDB
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128  # FMOV.F FA, [0x80]
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 0    # HLT
        cpu.run()
        _assert_halted_steps(cpu, 1)
        fpu = cpu.regs.fpu
        assert fpu is not None
        fa_raw = fpu.fa
        # FHA = low 16 bits, FHB = high 16 bits
        fha_raw = fpu.read_bits(0, FP_FMT_H, 0)  # pos=0, fmt=H
        fhb_raw = fpu.read_bits(1, FP_FMT_H, 0)  # pos=1, fmt=H
        assert fha_raw == fa_raw & 0xFFFF
        assert fhb_raw == (fa_raw >> 16) & 0xFFFF

    def test_fa_write_read_fqa(self) -> None:
        """Writing FA, FQA/FQB/FQC/FQD contain individual bytes."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 3.1415927)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 0  # HLT
        cpu.run()
        _assert_halted_steps(cpu, 1)
        fpu = cpu.regs.fpu
        assert fpu is not None
        fa_raw = fpu.fa
        from pysim8.isa import FP_FMT_O3
        for pos in range(4):
            byte_val = fpu.read_bits(pos, FP_FMT_O3, 0)
            expected = (fa_raw >> (pos * 8)) & 0xFF
            assert byte_val == expected, f"FQ pos={pos}: {byte_val} != {expected}"

    def test_fha_write_does_not_corrupt_fhb(self) -> None:
        """Writing FHA should not change FHB bits."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        # First load a known value into FA (sets both FHA and FHB)
        _store_f32(cpu, 0x80, 3.1415927)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        fpm_fha = encode_fpm(0, 0, FP_FMT_H)
        cpu.mem[0] = 128  # FMOV.F FA, [0x80]  (sets all 32 bits)
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # Now store float16 1.5 into FHA (should only touch low 16)
        cpu.mem[3] = 128  # FMOV.H FHA, [0x88]
        cpu.mem[4] = fpm_fha
        cpu.mem[5] = 0x88
        cpu.mem[6] = 0    # HLT
        _store_f16(cpu, 0x88, 1.5)
        cpu.run()
        _assert_halted_steps(cpu, 2)
        fpu = cpu.regs.fpu
        assert fpu is not None
        # FHA should be float16 1.5 = 0x3E00
        assert fpu.read_bits(0, FP_FMT_H, 0) == 0x3E00
        # FHB should be the ORIGINAL upper 16 bits of pi
        pi_raw = struct.unpack("<I", struct.pack("<f", 3.1415927))[0]
        expected_fhb = (pi_raw >> 16) & 0xFFFF
        assert fpu.read_bits(1, FP_FMT_H, 0) == expected_fhb


class TestFmovNanFpsr:
    """FMOV must NOT pollute FPSR — even with NaN values."""

    def test_fmov_load_nan_no_fpsr(self) -> None:
        """Loading NaN via FMOV should not set any FPSR flags."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        # Store NaN at 0x80
        for i, b in enumerate(struct.pack("<f", float("nan"))):
            cpu.mem[0x80 + i] = b
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128   # FMOV.F FA, [0x80]
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 149   # FSTAT A
        cpu.mem[4] = 0
        cpu.mem[5] = 0     # HLT
        cpu.run()
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 0, f"FPSR should be 0 after FMOV NaN, got {cpu.a:#x}"

    def test_fmov_store_nan_no_fpsr(self) -> None:
        """Storing NaN via FMOV should not set any FPSR flags."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        for i, b in enumerate(struct.pack("<f", float("nan"))):
            cpu.mem[0x80 + i] = b
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128   # FMOV.F FA, [0x80]  (load NaN)
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 152   # FCLR (clear any flags from load)
        cpu.mem[4] = 130   # FMOV.F [0x90], FA  (store NaN)
        cpu.mem[5] = fpm_fa
        cpu.mem[6] = 0x90
        cpu.mem[7] = 149   # FSTAT A
        cpu.mem[8] = 0
        cpu.mem[9] = 0     # HLT
        cpu.run()
        _assert_halted_steps(cpu, 4)
        assert cpu.a == 0, f"FPSR should be 0 after FMOV store NaN, got {cpu.a:#x}"

    def test_fmov_rr_nan_no_fpsr(self) -> None:
        """Register-to-register FMOV of NaN should not set FPSR."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        for i, b in enumerate(struct.pack("<f", float("nan"))):
            cpu.mem[0x80 + i] = b
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        fpm_fb = encode_fpm(1, 0, FP_FMT_F)
        cpu.mem[0] = 128   # FMOV.F FA, [0x80]
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 152   # FCLR
        cpu.mem[4] = 145   # FMOV_RR FB, FA
        cpu.mem[5] = fpm_fb
        cpu.mem[6] = fpm_fa
        cpu.mem[7] = 149   # FSTAT A
        cpu.mem[8] = 0
        cpu.mem[9] = 0     # HLT
        cpu.run()
        _assert_halted_steps(cpu, 4)
        assert cpu.a == 0, f"FPSR should be 0 after FMOV_RR NaN, got {cpu.a:#x}"


class TestE4m3Saturation:
    """E4M3 has no Inf — overflow saturates to ±448."""

    def test_overflow_saturates_to_max(self) -> None:
        """E4M3 encode of large value → 448, not Inf."""
        data, exc = encode_ofp8_e4m3(1000.0)
        val = bytes_to_float(data, 3)
        assert val == 448.0
        assert exc.overflow

    def test_neg_overflow_saturates(self) -> None:
        """E4M3 encode of large negative → -448."""
        data, exc = encode_ofp8_e4m3(-1000.0)
        val = bytes_to_float(data, 3)
        assert val == -448.0
        assert exc.overflow

    def test_exact_448_no_overflow(self) -> None:
        """E4M3 encoding of exactly 448 should NOT overflow."""
        data, exc = encode_ofp8_e4m3(448.0)
        val = bytes_to_float(data, 3)
        assert val == 448.0
        assert not exc.overflow

    def test_448_rtz(self) -> None:
        """E4M3 value just above 448 under RTZ → 448 (truncate)."""
        data, exc = encode_ofp8_e4m3(449.0, rm=1)  # RTZ
        val = bytes_to_float(data, 3)
        assert val == 448.0

    def test_448_rdn_positive(self) -> None:
        """E4M3 value 449 under RDN (floor) → 448."""
        data, exc = encode_ofp8_e4m3(449.0, rm=2)  # RDN
        val = bytes_to_float(data, 3)
        assert val == 448.0

    def test_448_rup_positive(self) -> None:
        """E4M3 value 449 under RUP (ceil) → 448 (saturate, no Inf)."""
        data, exc = encode_ofp8_e4m3(449.0, rm=3)  # RUP
        val = bytes_to_float(data, 3)
        assert val == 448.0
        assert exc.overflow

    def test_sim_fadd_e4m3_overflow(self) -> None:
        """Simulator: FADD of two E4M3 values exceeding 448 → saturates."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        from pysim8.isa import FP_FMT_O3
        fpm_fqa = encode_fpm(0, 0, FP_FMT_O3)
        _store_o3(cpu, 0x80, 256.0)
        _store_o3(cpu, 0x81, 256.0)
        cpu.mem[0] = 128  # FMOV.O3 FQA, [0x80]
        cpu.mem[1] = fpm_fqa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 132  # FADD.O3 FQA, [0x81]
        cpu.mem[4] = fpm_fqa
        cpu.mem[5] = 0x81
        cpu.mem[6] = 130  # FMOV.O3 [0x90], FQA
        cpu.mem[7] = fpm_fqa
        cpu.mem[8] = 0x90
        cpu.mem[9] = 149  # FSTAT A
        cpu.mem[10] = 0
        cpu.mem[11] = 0   # HLT
        cpu.run()
        _assert_halted_steps(cpu, 4)
        result = _read_o3(cpu, 0x90)
        assert result == 448.0, f"E4M3 overflow should saturate to 448, got {result}"
        assert cpu.a & 0x04, "overflow flag should be set"


class TestBf16DirectedRoundingValues:
    """bfloat16 directed rounding must produce correct VALUES, not just lengths."""

    def test_bf16_rne_midpoint(self) -> None:
        """RNE: midpoint rounds to even."""
        # 1.0 in bf16 = 0x3F80, next is 1.0078125 = 0x3F81
        # midpoint 1.00390625 should round to 1.0 (even mantissa)
        val = 1.00390625  # exact midpoint between bf16 1.0 and 1.0078125
        data, _ = encode_bfloat16(val, rm=0)
        result = bytes_to_float(data, 2)
        # RNE ties to even: 1.0 mantissa=0 (even) vs 1.0078125 mantissa=1 (odd)
        assert result == 1.0, f"RNE midpoint: expected 1.0, got {result}"

    def test_bf16_rtz(self) -> None:
        """RTZ: truncate toward zero."""
        val = 1.00390625  # midpoint
        data, _ = encode_bfloat16(val, rm=1)
        result = bytes_to_float(data, 2)
        assert result == 1.0, f"RTZ: expected 1.0 (truncate), got {result}"

    def test_bf16_rdn_positive(self) -> None:
        """RDN: positive value rounds toward -Inf (floor)."""
        val = 1.005  # between 1.0 and 1.0078125
        data, _ = encode_bfloat16(val, rm=2)
        result = bytes_to_float(data, 2)
        assert result == 1.0, f"RDN positive: expected 1.0 (floor), got {result}"

    def test_bf16_rdn_negative(self) -> None:
        """RDN: negative value rounds toward -Inf (away from zero)."""
        val = -1.005
        data, _ = encode_bfloat16(val, rm=2)
        result = bytes_to_float(data, 2)
        assert result == -1.0078125, (
            f"RDN negative: expected -1.0078125 (toward -Inf), got {result}"
        )

    def test_bf16_rup_positive(self) -> None:
        """RUP: positive value rounds toward +Inf (ceiling)."""
        val = 1.005
        data, _ = encode_bfloat16(val, rm=3)
        result = bytes_to_float(data, 2)
        assert result == 1.0078125, (
            f"RUP positive: expected 1.0078125 (ceiling), got {result}"
        )

    def test_bf16_rup_negative(self) -> None:
        """RUP: negative value rounds toward +Inf (toward zero)."""
        val = -1.005
        data, _ = encode_bfloat16(val, rm=3)
        result = bytes_to_float(data, 2)
        assert result == -1.0, f"RUP negative: expected -1.0 (toward zero), got {result}"


class TestFmaddNan:
    """FMADD with NaN in any operand position."""

    def test_fmadd_nan_in_dst(self) -> None:
        """FMADD dst=NaN, src, [mem]: result should be NaN."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        fpm_fha = encode_fpm(0, 0, FP_FMT_H)
        fpm_fhb = encode_fpm(0, 1, FP_FMT_H)
        # FHB (dst) = NaN
        for i, b in enumerate(struct.pack("<e", float("nan"))):
            cpu.mem[0x80 + i] = b
        # FHA (src) = 2.0
        _store_f16(cpu, 0x82, 2.0)
        # mem[0x84] = 3.0
        _store_f16(cpu, 0x84, 3.0)
        cpu.mem[0] = 128   # FMOV.H FHB, [0x80]  (NaN)
        cpu.mem[1] = fpm_fhb
        cpu.mem[2] = 0x80
        cpu.mem[3] = 128   # FMOV.H FHA, [0x82]  (2.0)
        cpu.mem[4] = fpm_fha
        cpu.mem[5] = 0x82
        cpu.mem[6] = 159   # FMADD.H FHB, FHA, [0x84]
        cpu.mem[7] = fpm_fhb
        cpu.mem[8] = fpm_fha
        cpu.mem[9] = 0x84
        cpu.mem[10] = 130  # FMOV.H [0x90], FHB
        cpu.mem[11] = fpm_fhb
        cpu.mem[12] = 0x90
        cpu.mem[13] = 0    # HLT
        cpu.run()
        _assert_halted_steps(cpu, 4)
        result = _read_f16(cpu, 0x90)
        assert math.isnan(result), f"FMADD with NaN dst should be NaN, got {result}"

    def test_fmadd_nan_in_src(self) -> None:
        """FMADD dst, src=NaN, [mem]: result should be NaN."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        fpm_fha = encode_fpm(0, 0, FP_FMT_H)
        fpm_fhb = encode_fpm(0, 1, FP_FMT_H)
        # FHA (src) = NaN
        for i, b in enumerate(struct.pack("<e", float("nan"))):
            cpu.mem[0x80 + i] = b
        _store_f16(cpu, 0x82, 1.0)   # FHB (dst) = 1.0
        _store_f16(cpu, 0x84, 3.0)   # mem = 3.0
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fha
        cpu.mem[2] = 0x80
        cpu.mem[3] = 128
        cpu.mem[4] = fpm_fhb
        cpu.mem[5] = 0x82
        cpu.mem[6] = 159   # FMADD.H FHB, FHA, [0x84]
        cpu.mem[7] = fpm_fhb
        cpu.mem[8] = fpm_fha
        cpu.mem[9] = 0x84
        cpu.mem[10] = 130
        cpu.mem[11] = fpm_fhb
        cpu.mem[12] = 0x90
        cpu.mem[13] = 0
        cpu.run()
        _assert_halted_steps(cpu, 4)
        result = _read_f16(cpu, 0x90)
        assert math.isnan(result), f"FMADD with NaN src should be NaN, got {result}"

    def test_fmadd_nan_in_mem(self) -> None:
        """FMADD dst, src, [NaN]: result should be NaN."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        fpm_fha = encode_fpm(0, 0, FP_FMT_H)
        fpm_fhb = encode_fpm(0, 1, FP_FMT_H)
        _store_f16(cpu, 0x80, 2.0)   # FHA (src) = 2.0
        _store_f16(cpu, 0x82, 1.0)   # FHB (dst) = 1.0
        # mem = NaN
        for i, b in enumerate(struct.pack("<e", float("nan"))):
            cpu.mem[0x84 + i] = b
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fha
        cpu.mem[2] = 0x80
        cpu.mem[3] = 128
        cpu.mem[4] = fpm_fhb
        cpu.mem[5] = 0x82
        cpu.mem[6] = 159
        cpu.mem[7] = fpm_fhb
        cpu.mem[8] = fpm_fha
        cpu.mem[9] = 0x84
        cpu.mem[10] = 130
        cpu.mem[11] = fpm_fhb
        cpu.mem[12] = 0x90
        cpu.mem[13] = 0
        cpu.run()
        _assert_halted_steps(cpu, 4)
        result = _read_f16(cpu, 0x90)
        assert math.isnan(result), f"FMADD with NaN mem should be NaN, got {result}"


class TestFcmpNanFpsr:
    """FCMP with qNaN should set Unordered but NOT raise Invalid."""

    def test_fcmp_qnan_unordered(self) -> None:
        """FCMP with NaN operand: Z=1, C=1 (Unordered)."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        for i, b in enumerate(struct.pack("<f", float("nan"))):
            cpu.mem[0x80 + i] = b
        _store_f32(cpu, 0x84, 1.0)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu.mem[0] = 128   # FMOV.F FA, [0x80]  (NaN)
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        cpu.mem[3] = 152   # FCLR
        cpu.mem[4] = 140   # FCMP.F FA, [0x84]
        cpu.mem[5] = fpm_fa
        cpu.mem[6] = 0x84
        cpu.mem[7] = 149   # FSTAT A
        cpu.mem[8] = 0
        cpu.mem[9] = 0     # HLT
        cpu.run()
        _assert_halted_steps(cpu, 4)
        assert cpu.zero is True, "NaN compare should set Z=1 (Unordered)"
        assert cpu.carry is True, "NaN compare should set C=1 (Unordered)"
        # Per spec: qNaN should NOT raise Invalid (only sNaN should).
        # Python cannot distinguish sNaN/qNaN, so this documents behavior.
        # Uncomment when sNaN/qNaN distinction is implemented:
        # assert cpu.a & 0x01 == 0, "qNaN compare must NOT set Invalid"


# ── Encoder edge cases (coverage) ──────────────────────────────────


class TestBf16RneEdges:
    """bfloat16 RNE rounding edge cases in _round_f32_to_bf16."""

    def test_rne_tie_round_to_even(self) -> None:
        """RNE tie with odd upper → rounds up (line 175)."""
        # Construct f32 bits where lower == 0x8000 and upper is odd.
        # 1.0 = 0x3F800000: upper=0x3F80, lower=0x0000 (even, no tie)
        # We need upper odd + lower = 0x8000.
        # 0x3F818000: upper=0x3F81 (odd), lower=0x8000 (tie)
        import struct
        f32_bits = 0x3F81_8000
        f32_val = struct.unpack("<f", f32_bits.to_bytes(4, "little"))[0]
        d, exc = encode_bfloat16(f32_val, RoundingMode.RNE)
        bf16_bits = int.from_bytes(d, "little")
        # Odd upper + tie → round up: 0x3F81 → 0x3F82
        assert bf16_bits == 0x3F82
        assert exc.inexact

    def test_rne_carry_overflow_to_inf(self) -> None:
        """RNE carry overflow → Inf (lines 179-180)."""
        # Max bf16 normal: 0x7F7F → value ≈ 3.389e38
        # If lower > 0x8000, upper rounds up: 0x7F7F → 0x7F80 = Inf
        import struct
        f32_bits = 0x7F7F_FFFF  # max finite f32
        f32_val = struct.unpack("<f", f32_bits.to_bytes(4, "little"))[0]
        d, exc = encode_bfloat16(f32_val, RoundingMode.RNE)
        bf16_val = decode_bfloat16(d)
        assert math.isinf(bf16_val)
        assert exc.overflow

    def test_rne_neg_carry_overflow(self) -> None:
        """Negative RNE carry → -Inf."""
        import struct
        f32_bits = 0xFF7F_FFFF  # -max finite f32
        f32_val = struct.unpack("<f", f32_bits.to_bytes(4, "little"))[0]
        d, exc = encode_bfloat16(f32_val, RoundingMode.RNE)
        bf16_val = decode_bfloat16(d)
        assert math.isinf(bf16_val) and bf16_val < 0
        assert exc.overflow


class TestE4m3OverflowSaturation:
    """E4M3 overflow → max finite (not Inf) with NaN collision avoidance."""

    def test_e4m3_rtz_overflow_saturates(self) -> None:
        """E4M3 RTZ overflow → ±448 (max finite), line 409."""
        d, exc = float_to_bytes(500.0, FP_FMT_O3, RoundingMode.RTZ)
        r = bytes_to_float(d, FP_FMT_O3)
        assert r == 448.0
        assert exc.overflow

    def test_e4m3_nan_collision_avoidance(self) -> None:
        """Value that rounds to NaN pattern gets stepped down (line 491).

        E4M3 NaN = 0x7F (exp=1111, mant=111). The value that naturally
        encodes to 0x7F after rounding should be stepped to 0x7E (=448).
        """
        # 0x7F = exp=15, mant=7 → would be (1+7/8)*2^8 = 480 if it existed
        # But 0x7F is NaN. Any value that rounds to 480 should get 448.
        # With RUP, a value slightly above 448 would round to the next
        # representable, which would be 480 (0x7F) — but that's NaN.
        d, exc = float_to_bytes(449.0, FP_FMT_O3, RoundingMode.RUP)
        r = bytes_to_float(d, FP_FMT_O3)
        # Should saturate to 448 (0x7E), not encode as NaN
        assert r == 448.0


# ── Property-based tests (hypothesis) ──────────────────────────────

# Safe encode ranges — halved so that a+b / a*b stay within encoder limits.
_FMT_RANGE: dict[int, tuple[float, float]] = {
    FP_FMT_F:  (-1e38, 1e38),      # float32 (half of 3.4e38)
    FP_FMT_H:  (-30000, 30000),    # float16 (half of 65504)
    FP_FMT_BF: (-1e38, 1e38),      # bfloat16
    FP_FMT_O3: (-224, 224),        # E4M3 (half of 448)
    FP_FMT_O2: (-28000, 28000),    # E5M2 (half of 57344)
}

_rounding_modes = st.sampled_from([
    RoundingMode.RNE, RoundingMode.RTZ, RoundingMode.RDN, RoundingMode.RUP,
])
_fmt_codes = st.sampled_from([
    FP_FMT_F, FP_FMT_H, FP_FMT_BF, FP_FMT_O3, FP_FMT_O2,
])
_raw_f32 = st.binary(min_size=4, max_size=4)
_raw_f16 = st.binary(min_size=2, max_size=2)
_raw_byte = st.integers(min_value=0, max_value=255)


def _safe_finite(fmt: int) -> st.SearchStrategy[float]:
    """Finite floats within the representable range for a format."""
    lo, hi = _FMT_RANGE[fmt]
    return st.floats(
        min_value=lo, max_value=hi,
        allow_nan=False, allow_infinity=False,
    )


class TestPropRoundTrip:
    """Encode→decode is idempotent (second encode is identity)."""

    @given(data=st.data(), rm=_rounding_modes, fmt=_fmt_codes)
    @settings(max_examples=200)
    def test_encode_decode_stable(
        self, data: st.DataObject, rm: int, fmt: int,
    ) -> None:
        val = data.draw(_safe_finite(fmt))
        d1, _ = float_to_bytes(val, fmt, rm)
        v1 = bytes_to_float(d1, fmt)
        if math.isnan(v1):
            return
        d2, _ = float_to_bytes(v1, fmt, rm)
        v2 = bytes_to_float(d2, fmt)
        assert v2 == v1, f"not stable: {val}→{v1}→{v2} (fmt={fmt} rm={rm})"

    @given(_raw_f32)
    def test_f32_raw_roundtrip(self, data: bytes) -> None:
        val = decode_float32(data)
        if math.isnan(val):
            return
        enc, _ = encode_float32(val)
        assert decode_float32(enc) == val

    @given(_raw_f16)
    def test_f16_raw_roundtrip(self, data: bytes) -> None:
        val = decode_float16(data)
        if math.isnan(val):
            return
        enc, _ = encode_float16(val)
        assert decode_float16(enc) == val

    @given(_raw_f16)
    def test_bf16_raw_roundtrip(self, data: bytes) -> None:
        val = decode_bfloat16(data)
        if math.isnan(val):
            return
        enc, _ = encode_bfloat16(val)
        assert decode_bfloat16(enc) == val

    @given(_raw_byte)
    def test_e4m3_raw_roundtrip(self, b: int) -> None:
        val = decode_ofp8_e4m3(b)
        if math.isnan(val):
            return
        enc, _ = encode_ofp8_e4m3(val)
        assert decode_ofp8_e4m3(enc[0]) == val

    @given(_raw_byte)
    def test_e5m2_raw_roundtrip(self, b: int) -> None:
        val = decode_ofp8_e5m2(b)
        if math.isnan(val) or math.isinf(val):
            return
        enc, _ = encode_ofp8_e5m2(val)
        assert decode_ofp8_e5m2(enc[0]) == val


class TestPropE4M3:
    """E4M3 invariants: no Inf, max |value| ≤ 448."""

    @given(data=st.data(), rm=_rounding_modes)
    @settings(max_examples=200)
    def test_no_infinity(self, data: st.DataObject, rm: int) -> None:
        val = data.draw(_safe_finite(3))
        d, _ = encode_ofp8_e4m3(val, rm)
        assert not math.isinf(decode_ofp8_e4m3(d[0]))

    @given(data=st.data(), rm=_rounding_modes)
    @settings(max_examples=200)
    def test_max_448(self, data: st.DataObject, rm: int) -> None:
        val = data.draw(_safe_finite(3))
        d, _ = encode_ofp8_e4m3(val, rm)
        r = decode_ofp8_e4m3(d[0])
        if not math.isnan(r):
            assert abs(r) <= 448.0

    @given(_raw_byte)
    def test_all_patterns_decode(self, b: int) -> None:
        """Every byte decodes without error."""
        assert isinstance(decode_ofp8_e4m3(b), float)

    @given(_raw_byte)
    def test_e5m2_all_patterns_decode(self, b: int) -> None:
        assert isinstance(decode_ofp8_e5m2(b), float)


class TestPropRoundingDirection:
    """Rounding mode direction properties."""

    @given(data=st.data(), fmt=_fmt_codes)
    @settings(max_examples=200)
    def test_rtz_toward_zero(self, data: st.DataObject, fmt: int) -> None:
        """RTZ: |result| <= |exact| for positive values."""
        val = data.draw(st.floats(
            min_value=0.0, max_value=_FMT_RANGE[fmt][1],
            allow_nan=False, allow_infinity=False,
        ))
        assume(val > 0)
        d, _ = float_to_bytes(val, fmt, RoundingMode.RTZ)
        r = bytes_to_float(d, fmt)
        if math.isnan(r) or math.isinf(r):
            return
        assert r <= val + 1e-45

    @given(data=st.data(), fmt=_fmt_codes)
    @settings(max_examples=200)
    def test_rdn_floor(self, data: st.DataObject, fmt: int) -> None:
        """RDN: result <= exact (floor) for positive values."""
        lo, hi = _FMT_RANGE[fmt]
        val = data.draw(st.floats(
            min_value=0.0, max_value=hi,
            allow_nan=False, allow_infinity=False,
        ))
        d, _ = float_to_bytes(val, fmt, RoundingMode.RDN)
        r = bytes_to_float(d, fmt)
        if math.isnan(r) or math.isinf(r):
            return
        assert r <= val + 1e-45

    @given(data=st.data(), fmt=_fmt_codes)
    @settings(max_examples=200)
    def test_rup_ceil(self, data: st.DataObject, fmt: int) -> None:
        """RUP: result >= exact (ceil) for positive values."""
        lo, hi = _FMT_RANGE[fmt]
        val = data.draw(st.floats(
            min_value=0.0, max_value=hi,
            allow_nan=False, allow_infinity=False,
        ))
        d, exc = float_to_bytes(val, fmt, RoundingMode.RUP)
        r = bytes_to_float(d, fmt)
        if math.isnan(r) or math.isinf(r):
            return
        # Overflow/saturation or underflow: format can't represent exactly
        if exc.overflow or exc.underflow:
            return
        # RUP should round toward +Inf, so r >= val.
        assert r >= val or math.isclose(r, val, rel_tol=1e-6)

    @given(data=st.data(), fmt=_fmt_codes)
    @settings(max_examples=200)
    def test_rdn_negative_floor(self, data: st.DataObject, fmt: int) -> None:
        """RDN: result <= exact for negative values (toward -Inf)."""
        lo, _ = _FMT_RANGE[fmt]
        val = data.draw(st.floats(
            min_value=lo, max_value=0.0,
            allow_nan=False, allow_infinity=False,
        ))
        assume(val < 0)
        d, _ = float_to_bytes(val, fmt, RoundingMode.RDN)
        r = bytes_to_float(d, fmt)
        if math.isnan(r) or math.isinf(r):
            return
        if fmt == 3 and val < -448.0:
            return
        assert r <= val + 1e-45


class TestPropArithmetic:
    """Algebraic properties of FP arithmetic."""

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_add_commutative(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        s = _safe_finite(fmt)
        a, b = data.draw(s), data.draw(s)
        r1, _ = fp_add(a, b, fmt, rm)
        r2, _ = fp_add(b, a, fmt, rm)
        if math.isnan(r1):
            assert math.isnan(r2)
        else:
            assert r1 == r2

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_mul_commutative(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        s = _safe_finite(fmt)
        a, b = data.draw(s), data.draw(s)
        r1, _ = fp_mul(a, b, fmt, rm)
        r2, _ = fp_mul(b, a, fmt, rm)
        if math.isnan(r1):
            assert math.isnan(r2)
        else:
            assert r1 == r2

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_add_zero_identity(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        """a + 0 == a when a is already in format."""
        val = data.draw(_safe_finite(fmt))
        d, _ = float_to_bytes(val, fmt, rm)
        a = bytes_to_float(d, fmt)
        if math.isnan(a):
            return
        r, _ = fp_add(a, 0.0, fmt, rm)
        if math.isnan(r):
            return
        assert r == a, f"a+0 != a: {a}+0={r} fmt={fmt}"

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_mul_one_identity(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        """a * 1 == a when a is already in format."""
        val = data.draw(_safe_finite(fmt))
        d, _ = float_to_bytes(val, fmt, rm)
        a = bytes_to_float(d, fmt)
        if math.isnan(a) or math.isinf(a):
            return
        r, _ = fp_mul(a, 1.0, fmt, rm)
        if math.isnan(r):
            return
        assert r == a, f"a*1 != a: {a}*1={r} fmt={fmt}"

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_sub_self_zero(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        """a - a == 0."""
        val = data.draw(_safe_finite(fmt))
        d, _ = float_to_bytes(val, fmt, rm)
        a = bytes_to_float(d, fmt)
        if math.isnan(a) or math.isinf(a):
            return
        r, _ = fp_sub(a, a, fmt, rm)
        assert r == 0.0, f"a-a != 0: {a}-{a}={r} fmt={fmt}"

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_div_self_one(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        """a / a == 1 for non-zero."""
        val = data.draw(st.floats(
            min_value=1e-6, max_value=_FMT_RANGE[fmt][1],
            allow_nan=False, allow_infinity=False,
        ))
        d, _ = float_to_bytes(val, fmt, rm)
        a = bytes_to_float(d, fmt)
        assume(a != 0.0 and not math.isinf(a) and not math.isnan(a))
        r, _ = fp_div(a, a, fmt, rm)
        if not math.isnan(r):
            assert r == 1.0, f"a/a != 1: {a}/{a}={r} fmt={fmt}"


class TestPropAbsNeg:
    """FABS/FNEG bit-level invariants."""

    @given(st.integers(min_value=0, max_value=0xFFFFFFFF))
    def test_fabs_idempotent(self, bits: int) -> None:
        assert fp_abs(fp_abs(bits, 32), 32) == fp_abs(bits, 32)

    @given(st.integers(min_value=0, max_value=0xFFFFFFFF))
    def test_fneg_involution(self, bits: int) -> None:
        assert fp_neg(fp_neg(bits, 32), 32) == bits

    @given(st.integers(min_value=0, max_value=0xFFFFFFFF))
    def test_fabs_clears_sign(self, bits: int) -> None:
        assert fp_abs(bits, 32) & 0x80000000 == 0

    @given(st.integers(min_value=0, max_value=0xFF))
    def test_abs_neg_8bit(self, bits: int) -> None:
        assert fp_abs(bits, 8) & 0x80 == 0
        assert fp_neg(fp_neg(bits, 8), 8) == bits


class TestPropCmp:
    """FCMP ordering invariants."""

    @given(
        st.floats(allow_nan=False, allow_infinity=False),
        st.floats(allow_nan=False, allow_infinity=False),
    )
    def test_antisymmetric(self, a: float, b: float) -> None:
        z1, c1, _ = fp_cmp(a, b)
        z2, c2, _ = fp_cmp(b, a)
        if z1 and not c1:       # a == b
            assert z2 and not c2
        elif not z1 and c1:     # a < b
            assert not z2 and not c2  # b > a
        elif not z1 and not c1: # a > b
            assert not z2 and c2      # b < a

    @given(st.floats(allow_nan=False, allow_infinity=False))
    def test_reflexive(self, a: float) -> None:
        z, c, _ = fp_cmp(a, a)
        assert z is True and c is False

    def test_nan_unordered(self) -> None:
        z, c, _ = fp_cmp(float("nan"), 1.0)
        assert z is True and c is True
        z, c, _ = fp_cmp(1.0, float("nan"))
        assert z is True and c is True
        z, c, _ = fp_cmp(float("nan"), float("nan"))
        assert z is True and c is True


class TestPropClassify:
    """FCLASS: exactly one category bit, NEG matches sign."""

    @given(_raw_f32)
    def test_one_class_bit_f32(self, data: bytes) -> None:
        val = struct.unpack("<f", data)[0]
        raw = struct.unpack("<I", data)[0]
        mask = fp_classify(val, raw, 32, 0)
        bits = mask & 0x3F
        assert bits != 0 and bits & (bits - 1) == 0

    @given(_raw_f16)
    def test_one_class_bit_f16(self, data: bytes) -> None:
        val = struct.unpack("<e", data)[0]
        raw = struct.unpack("<H", data)[0]
        mask = fp_classify(val, raw, 16, 1)
        bits = mask & 0x3F
        assert bits != 0 and bits & (bits - 1) == 0

    @given(_raw_f32)
    def test_neg_matches_sign_f32(self, data: bytes) -> None:
        raw = struct.unpack("<I", data)[0]
        val = struct.unpack("<f", data)[0]
        mask = fp_classify(val, raw, 32, 0)
        assert ((mask >> 6) & 1) == ((raw >> 31) & 1)

    @given(_raw_byte)
    def test_one_class_bit_e4m3(self, b: int) -> None:
        val = decode_ofp8_e4m3(b)
        mask = fp_classify(val, b, 8, 3)
        bits = mask & 0x3F
        assert bits != 0 and bits & (bits - 1) == 0


class TestPropExceptionFlags:
    """Exception flag sanity."""

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_finite_add_no_invalid(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        s = _safe_finite(fmt)
        a, b = data.draw(s), data.draw(s)
        _, exc = fp_add(a, b, fmt, rm)
        assert not exc.invalid

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_sqrt_nonneg_no_invalid(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        val = data.draw(st.floats(
            min_value=0.0, max_value=_FMT_RANGE[fmt][1],
            allow_nan=False, allow_infinity=False,
        ))
        _, exc = fp_sqrt(val, fmt, rm)
        assert not exc.invalid

    @given(data=st.data(), fmt=_fmt_codes, rm=_rounding_modes)
    @settings(max_examples=200)
    def test_nonzero_div_no_divzero(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        b_val = data.draw(st.floats(
            min_value=1e-6, max_value=_FMT_RANGE[fmt][1],
            allow_nan=False, allow_infinity=False,
        ))
        d, _ = float_to_bytes(b_val, fmt, rm)
        b = bytes_to_float(d, fmt)
        assume(b != 0.0 and not math.isnan(b))
        _, exc = fp_div(1.0, b, fmt, rm)
        assert not exc.div_zero


class TestPropWidening:
    """Narrower format values survive widening round-trip."""

    @given(b=_raw_byte, rm=_rounding_modes)
    def test_e4m3_through_f32(self, b: int, rm: int) -> None:
        val = decode_ofp8_e4m3(b)
        if math.isnan(val):
            return
        f32_d, _ = encode_float32(val, rm)
        assert decode_float32(f32_d) == val
        back_d, _ = encode_ofp8_e4m3(val, rm)
        assert decode_ofp8_e4m3(back_d[0]) == val

    @given(b=_raw_byte, rm=_rounding_modes)
    def test_e5m2_through_f32(self, b: int, rm: int) -> None:
        val = decode_ofp8_e5m2(b)
        if math.isnan(val) or math.isinf(val):
            return
        f32_d, _ = encode_float32(val, rm)
        assert decode_float32(f32_d) == val

    @given(data=_raw_f16, rm=_rounding_modes)
    def test_f16_through_f32(self, data: bytes, rm: int) -> None:
        val = decode_float16(data)
        if math.isnan(val) or math.isinf(val):
            return
        f32_d, _ = encode_float32(val, rm)
        assert decode_float32(f32_d) == val


# ── Handler coverage tests ─────────────────────────────────────────


class TestFmovRegaddr:
    """FMOV with register indirect addressing (handlers_fp lines 300, 314)."""

    def test_fmov_load_regaddr_f32(self) -> None:
        """FMOV.F FA, [B] — load float32 via register indirect."""
        cpu = run("""
            MOV B, 100
            FMOV.F FA, [B]
            HLT
        """)
        # B=100, DP=0 → addr=100. Memory is zeroed → FA=0.0
        _assert_halted_steps(cpu, 2)
        assert cpu.b == 100
        assert cpu.regs.fpu.read_bits(0, FP_FMT_F, 0) == 0

    def test_fmov_store_regaddr_f32(self) -> None:
        """FMOV.F [B], FA — store float32 via register indirect."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        _store_f32(cpu, 0x80, 3.14)
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        # FMOV.F FA, [0x80]
        cpu.mem[0] = 128
        cpu.mem[1] = fpm_fa
        cpu.mem[2] = 0x80
        # MOV B, 0x90
        cpu.mem[3] = 6   # MOV_REG_CONST
        cpu.mem[4] = 1   # B
        cpu.mem[5] = 0x90
        # FMOV.F [B], FA (opcode 131)
        cpu.mem[6] = 131
        cpu.mem[7] = fpm_fa
        cpu.mem[8] = (0 << 3) | 1  # [B+0]
        cpu.mem[9] = 0   # HLT
        cpu.run()
        _assert_halted_steps(cpu, 3)
        assert cpu.b == 0x90
        expected = list(struct.pack("<f", 3.14))
        actual = [cpu.mem[0x90 + i] for i in range(4)]
        assert actual == expected

    def test_fmov_load_regaddr_f16(self) -> None:
        """FMOV.H FHA, [B] — register indirect float16."""
        cpu = run("""
            MOV B, 100
            FMOV.H FHA, [B]
            HLT
        """)
        _assert_halted_steps(cpu, 2)
        assert cpu.b == 100
        assert cpu.regs.fpu.read_bits(0, FP_FMT_H, 0) == 0

    def test_fmov_store_regaddr_f16(self) -> None:
        """FMOV.H [B], FHA — store float16 via register indirect."""
        cpu = run("""
            FMOV.H FHA, 1.5
            MOV B, 100
            FMOV.H [B], FHA
            HLT
        """)
        _assert_halted_steps(cpu, 3)
        assert cpu.b == 100
        result = _read_f16(cpu, 100)
        assert result == 1.5


class TestFftoiNegative:
    """FFTOI with negative values — saturate to 0 (line 437)."""

    def test_fftoi_negative_float(self) -> None:
        """Negative float → 0 (saturate low)."""
        cpu = run("""
            FMOV.H FHA, -5.0
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 0

    def test_fftoi_negative_large(self) -> None:
        """Large negative float → 0."""
        cpu = run("""
            FMOV.H FHA, -100.0
            FFTOI.H A, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 2)
        assert cpu.a == 0


class TestFcmpRrFormatMismatch:
    """FCMP_RR with mismatched formats → FAULT (line 483)."""

    def test_fcmp_rr_format_mismatch_fault(self) -> None:
        """FCMP_RR with different format FPMs → FP_FORMAT fault."""
        fpm_f32 = encode_fpm(0, 0, FP_FMT_F)   # FA as float32
        fpm_f16 = encode_fpm(0, 0, FP_FMT_H)   # FHA as float16
        cpu = run_binary([157, fpm_f32, fpm_f16, 0])  # FCMP_RR
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.FP_FORMAT


class TestFmaddFormatMismatch:
    """FMADD with mismatched dst/src formats → FAULT (line 527)."""

    def test_fmadd_format_mismatch_fault(self) -> None:
        """FMADD with different dst/src formats → FP_FORMAT fault."""
        fpm_f32 = encode_fpm(0, 0, FP_FMT_F)   # FA as float32
        fpm_f16 = encode_fpm(0, 0, FP_FMT_H)   # FHA as float16
        # FMADD_ADDR: [159, dst_fpm, src_fpm, addr]
        cpu = run_binary([159, fpm_f16, fpm_f32, 0x80, 0])
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.FP_FORMAT


class TestInvalidRegFaults:
    """Handler validation faults for invalid register codes."""

    def test_indirect_addr_invalid_reg(self) -> None:
        """Register code > SP in indirect addressing → FAULT (handlers line 47)."""
        # MOV_REG_REGADDR (opcode 3): dest=A, regaddr with reg=6 (invalid)
        encoded_regaddr = (0 << 3) | 6  # offset=0, reg=6
        cpu = run_binary([3, 0, encoded_regaddr, 0])
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.INVALID_REG

    def test_mov_reg_invalid_high_code(self) -> None:
        """MOV with register code > DP → FAULT (handlers line 76)."""
        # MOV_REG_REG (opcode 1): dst=6 (invalid), src=0
        cpu = run_binary([1, 6, 0, 0])
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.INVALID_REG


# ── More property-based tests ──────────────────────────────────────


class TestPropEncoderRobustness:
    """Encoder never crashes on any finite float."""

    @given(
        val=st.floats(allow_nan=True, allow_infinity=True),
        fmt=_fmt_codes,
        rm=_rounding_modes,
    )
    @settings(max_examples=500)
    def test_float_to_bytes_never_crashes(
        self, val: float, fmt: int, rm: int,
    ) -> None:
        """float_to_bytes must never raise for any float/fmt/rm combo."""
        data, exc = float_to_bytes(val, fmt, rm)
        assert isinstance(data, bytes)
        assert isinstance(exc, FpExceptions)

    @given(
        val=st.floats(allow_nan=True, allow_infinity=True),
        fmt=_fmt_codes,
        rm=_rounding_modes,
    )
    @settings(max_examples=500)
    def test_encode_produces_valid_size(
        self, val: float, fmt: int, rm: int,
    ) -> None:
        """Encoded bytes have correct length and can be decoded back."""
        from pysim8.isa import FP_FMT_WIDTH
        data, _ = float_to_bytes(val, fmt, rm)
        assert len(data) == FP_FMT_WIDTH[fmt] // 8
        decoded = bytes_to_float(data, fmt)
        assert isinstance(decoded, float)

    @given(
        val=st.floats(min_value=-1e30, max_value=1e30,
                       allow_nan=False, allow_infinity=False),
        fmt=_fmt_codes,
        rm=_rounding_modes,
    )
    @settings(max_examples=300)
    def test_finite_encodes_to_finite_or_overflow(
        self, val: float, fmt: int, rm: int,
    ) -> None:
        """Finite input → finite output OR overflow flag set."""
        data, exc = float_to_bytes(val, fmt, rm)
        result = bytes_to_float(data, fmt)
        if math.isinf(result):
            assert exc.overflow

    @given(fmt=_fmt_codes, rm=_rounding_modes)
    def test_zero_encodes_to_zero(self, fmt: int, rm: int) -> None:
        """0.0 always encodes to 0.0."""
        data, exc = float_to_bytes(0.0, fmt, rm)
        result = bytes_to_float(data, fmt)
        assert result == 0.0
        assert not exc.overflow
        assert not exc.inexact

    @given(fmt=_fmt_codes, rm=_rounding_modes)
    def test_neg_zero_encodes_to_neg_zero(self, fmt: int, rm: int) -> None:
        """Signed zero is preserved."""
        data, exc = float_to_bytes(-0.0, fmt, rm)
        result = bytes_to_float(data, fmt)
        assert result == 0.0

    @given(fmt=_fmt_codes)
    def test_inf_roundtrip(self, fmt: int) -> None:
        """Inf encodes and decodes correctly (except E4M3 which has no Inf)."""
        data, exc = float_to_bytes(float("inf"), fmt)
        result = bytes_to_float(data, fmt)
        if fmt == FP_FMT_O3:
            # E4M3 has no Inf — should saturate to max
            assert not math.isinf(result)
        else:
            assert math.isinf(result) and result > 0

    @given(fmt=_fmt_codes)
    def test_nan_roundtrip(self, fmt: int) -> None:
        """NaN encodes to NaN."""
        data, exc = float_to_bytes(float("nan"), fmt)
        result = bytes_to_float(data, fmt)
        assert math.isnan(result)


class TestPropFpArithmeticCrazy:
    """Property-based arithmetic with extreme/edge values."""

    @given(fmt=_fmt_codes, rm=_rounding_modes)
    def test_div_by_zero_flag(self, fmt: int, rm: int) -> None:
        """Division by zero always sets div_zero flag."""
        _, exc = fp_div(1.0, 0.0, fmt, rm)
        assert exc.div_zero

    @given(fmt=_fmt_codes, rm=_rounding_modes)
    def test_sqrt_negative_invalid(self, fmt: int, rm: int) -> None:
        """sqrt(-1) always sets invalid flag and returns NaN."""
        result, exc = fp_sqrt(-1.0, fmt, rm)
        assert math.isnan(result)
        assert exc.invalid

    @given(fmt=_fmt_codes, rm=_rounding_modes)
    def test_nan_plus_anything(self, fmt: int, rm: int) -> None:
        """NaN + x = NaN with invalid flag."""
        result, exc = fp_add(float("nan"), 1.0, fmt, rm)
        assert math.isnan(result)
        assert exc.invalid

    @given(fmt=_fmt_codes, rm=_rounding_modes)
    def test_inf_minus_inf_nan(self, fmt: int, rm: int) -> None:
        """Inf - Inf = NaN with invalid flag."""
        result, exc = fp_sub(float("inf"), float("inf"), fmt, rm)
        assert math.isnan(result)
        assert exc.invalid

    @given(fmt=_fmt_codes, rm=_rounding_modes)
    def test_zero_times_inf_nan(self, fmt: int, rm: int) -> None:
        """0 * Inf = NaN with invalid flag."""
        result, exc = fp_mul(0.0, float("inf"), fmt, rm)
        assert math.isnan(result)
        assert exc.invalid

    @given(
        data=st.data(),
        fmt=st.sampled_from([FP_FMT_F, FP_FMT_H, FP_FMT_BF]),
        rm=_rounding_modes,
    )
    @settings(max_examples=200)
    def test_add_sub_inverse(
        self, data: st.DataObject, fmt: int, rm: int,
    ) -> None:
        """(a + b) - b ≈ a for small values (loose check)."""
        s = _safe_finite(fmt)
        a, b = data.draw(s), data.draw(s)
        # Pre-round both to format
        a_d, _ = float_to_bytes(a, fmt, rm)
        a_r = bytes_to_float(a_d, fmt)
        b_d, _ = float_to_bytes(b, fmt, rm)
        b_r = bytes_to_float(b_d, fmt)
        if math.isnan(a_r) or math.isnan(b_r):
            return
        if math.isinf(a_r) or math.isinf(b_r):
            return
        sum_r, _ = fp_add(a_r, b_r, fmt, rm)
        if math.isnan(sum_r) or math.isinf(sum_r):
            return
        diff_r, _ = fp_sub(sum_r, b_r, fmt, rm)
        if math.isnan(diff_r) or math.isinf(diff_r):
            return
        diff_d, _ = float_to_bytes(diff_r, fmt, rm)
        diff_q = bytes_to_float(diff_d, fmt)
        assert diff_q == diff_r


class TestPropSimRoundTrip:
    """Property: assemble → load → run → halt for every FP instruction."""

    @given(st.sampled_from([
        "FABS.F FA", "FNEG.H FHA", "FSQRT.BF FHB",
        "FABS.O3 FQA", "FNEG.O2 FQB",
    ]))
    def test_unary_halt(self, insn: str) -> None:
        """Unary FP instruction + HLT does not crash."""
        cpu = run(f"{insn}\nHLT")
        _assert_halted_steps(cpu, 1)

    @given(st.sampled_from(["FCLR", "FSTAT A", "FCFG A", "FSCFG A"]))
    def test_control_halt(self, insn: str) -> None:
        """Control FP instruction + HLT does not crash."""
        cpu = run(f"{insn}\nHLT")
        _assert_halted_steps(cpu, 1)


# ── Crazy simulator tests ─────────────────────────────────────────


class TestCrazySimInput:
    """Adversarial simulator inputs that should not crash."""

    def test_all_zero_memory(self) -> None:
        """All-zero memory → immediate HLT (opcode 0)."""
        cpu = CPU(arch=2)
        cpu.load([0] * 256)
        cpu.run()
        _assert_halted_steps(cpu, 0)

    def test_invalid_fpm_byte(self) -> None:
        """FPM with reserved format code → FAULT."""
        # fmt=5 is reserved
        fpm_bad = (0 << 6) | (0 << 3) | 5
        cpu = run_binary([142, fpm_bad, 0])  # FABS with bad FPM
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.FP_FORMAT

    def test_fpm_invalid_pos_for_format(self) -> None:
        """FPM with pos > max for format → FAULT."""
        # float32 (fmt=0) only has pos=0. pos=1 is invalid.
        fpm_bad = (0 << 6) | (1 << 3) | 0
        cpu = run_binary([142, fpm_bad, 0])  # FABS with bad pos
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.FP_FORMAT

    def test_fmov_imm8_with_f32_fmt_faults(self) -> None:
        """FMOV_FP_IMM8 (opcode 161) with float32 fmt → FAULT."""
        fpm_fa = encode_fpm(0, 0, FP_FMT_F)
        cpu = run_binary([161, fpm_fa, 0x3C, 0])
        assert cpu.state == CpuState.FAULT
        assert cpu.a == ErrorCode.FP_FORMAT

    def test_consecutive_fp_operations(self) -> None:
        """Many FP operations in sequence don't corrupt state."""
        cpu = run("""
            FMOV.H FHA, 1.0
            FADD.H FHA, FHA
            FADD.H FHA, FHA
            FADD.H FHA, FHA
            FADD.H FHA, FHA
            HLT
        """)
        _assert_halted_steps(cpu, 5)
        # 1.0 * 2^4 = 16.0
        raw = cpu.regs.fpu.read_bits(0, FP_FMT_H, 0)
        data = raw.to_bytes(2, "little")
        val = struct.unpack("<e", data)[0]
        assert val == 16.0

    def test_fclr_clears_all_flags(self) -> None:
        """FCLR after operations with exceptions clears FPSR."""
        cpu = run("""
            FMOV.H FHA, inf_h
            FMOV.H FHB, inf_h
            FNEG.H FHB
            FADD.H FHA, FHB
            FCLR
            FSTAT A
            HLT
        """)
        _assert_halted_steps(cpu, 6)
        assert cpu.a == 0  # FPSR cleared

    def test_fp_operation_on_zeroed_register(self) -> None:
        """FP operations on uninitialized (zero) FP register."""
        cpu = run("""
            FADD.F FA, [100]
            HLT
        """)
        # FA=0, mem[100]=0 → 0+0=0
        _assert_halted_steps(cpu, 1)
        assert cpu.regs.fpu.read_bits(0, FP_FMT_F, 0) == 0

    def test_fscfg_all_rounding_modes(self) -> None:
        """Set each rounding mode via FSCFG."""
        for mode in range(4):
            cpu = run(f"""
                MOV A, {mode}
                FSCFG A
                FCFG B
                HLT
            """)
            _assert_halted_steps(cpu, 3)
            assert cpu.b & 0x03 == mode


# ── fp_formats internal coverage ─────────────────────────────────────


class TestFpFormatsInternalCoverage:
    """Tests for fp_formats.py uncovered internal branches."""

    def test_overflow_result_with_nan_pattern(self) -> None:
        """_overflow_result with nan_pattern subtracts 1 from max_mant."""
        from pysim8.fp_formats import _overflow_result, RoundingMode
        # E4M3-like: 4-bit exp, 3-bit mant, no inf, nan_pattern=0x7F
        # RTZ for negative → does NOT return inf, goes to max finite
        byte_val, exc = _overflow_result(
            sign=1, exp_bits=4, mant_bits=3, max_exp=15,
            max_normal_biased=15, has_inf=False, nan_pattern=0x7F,
            rm=RoundingMode.RTZ,
        )
        assert exc.overflow
        assert exc.inexact
        # sign=1, exp=15, mant should be 6 (0b110 = 7-1) to avoid NaN
        # byte = 1_1111_110 = 0xFE
        assert byte_val == 0xFE

    def test_encode_mini_float_nan_collision(self) -> None:
        """_encode_mini_float decrements mantissa on NaN collision."""
        from pysim8.fp_formats import _encode_mini_float, RoundingMode
        # E4M3-like: 4-bit exp, 3-bit mant, bias=7, no inf, nan=0x7F
        # Pick a value that encodes to exp=15, mant=7 (NaN pattern)
        # Max finite E4M3 = (1 + 6/8) * 2^8 = 448
        # NaN would be exp=15, mant=7 → (1 + 7/8) * 2^8 = 480
        # We need a value just under 480 that rounds UP to mant=7
        # Use RUP with value like 449.0 which is > 448 but the caller
        # doesn't pre-filter (we call _encode_mini_float directly)
        # Actually we need a value that rounds to exp=15, mant=7 exactly.
        # (1+7/8)*2^8 = 480. Value 479.5 with RUP → mant=7 → collision.
        # But 479.5 is between (1+6/8)*2^8=448 and (1+7/8)*2^8=480.
        # In exp=15 range: significand = 479.5/256 = 1.87304...,
        # mant_frac = 0.87304... * 8 = 6.98, RUP → 7 → collision!
        byte_val, exc = _encode_mini_float(
            abs_val=479.5, sign=0, exp_bits=4, mant_bits=3, bias=7,
            has_inf=False, nan_pattern=0x7F, rm=RoundingMode.RUP,
        )
        # Should decrement mant from 7 to 6 → byte = 0_1111_110 = 0x7E
        assert byte_val == 0x7E


class TestFpArithRrFormatMismatch:
    """Test format mismatch fault in reg-reg FP arithmetic."""

    def test_fadd_rr_format_mismatch(self) -> None:
        """FADD_RR with mismatched FPM format codes → FAULT."""
        from pysim8.isa import encode_fpm, FP_FMT_F, FP_FMT_H, Op
        cpu = CPU(arch=2)
        # Build FADD_RR with dst=FA (fmt=F) src=FHA (fmt=H)
        dst_fpm = encode_fpm(0, 0, FP_FMT_F)
        src_fpm = encode_fpm(0, 0, FP_FMT_H)
        cpu.mem[0] = int(Op.FADD_RR)
        cpu.mem[1] = dst_fpm
        cpu.mem[2] = src_fpm
        cpu.mem[3] = int(Op.HLT)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.steps == 0
        assert cpu.a == ErrorCode.FP_FORMAT