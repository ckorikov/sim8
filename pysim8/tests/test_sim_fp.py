"""FP simulator tests for arch=2."""

import math
import struct

import pytest

from pysim8.asm import assemble
from pysim8.sim import CPU, CpuState
from pysim8.sim.errors import ErrorCode


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


# ── FMOV ─────────────────────────────────────────────────────────────

# FPM encoding: encode_fpm(phys=0, pos=0, fmt=0) for FA = 0x00
# For FHA (pos=0, fmt=1): encode_fpm(0, 0, 1) = 0x01
# For FHB (pos=1, fmt=1): encode_fpm(0, 1, 1) = 0x09

from pysim8.isa import encode_fpm, FP_FMT_F, FP_FMT_H


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
        assert cpu.state == CpuState.HALTED
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
        assert cpu.state == CpuState.HALTED
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
        assert cpu2.state == CpuState.HALTED
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
        assert cpu.state == CpuState.HALTED  # NOT FAULT
        assert cpu.a & 0x02 != 0  # DZ flag set


# ── FP_FORMAT fault ──────────────────────────────────────────────────


class TestFpFormatFault:
    def test_invalid_fpm_faults(self) -> None:
        """Invalid FPM byte (phys=1) causes FAULT(12)."""
        cpu = CPU(arch=2)
        # FABS opcode (142) + FPM=0x40 (phys=1, invalid in v2)
        cpu.load([142, 0x40, 0])
        cpu.run()
        assert cpu.state == CpuState.FAULT
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
        assert cpu.b == 1  # rounding mode set to RTZ
        assert cpu.regs.fpu is not None
        assert cpu.regs.fpu.rounding_mode == 1

    def test_fscfg_masks_reserved_bits(self) -> None:
        """FSCFG only uses bits [1:0]."""
        cpu = CPU(arch=2)
        # MOV A, 0xFF; FSCFG A; FCFG B; HLT
        cpu.load([6, 0, 0xFF, 151, 0, 150, 1, 0])
        cpu.run()
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
        assert _read_f32(cpu, 0x90) == 2.0


# ── Arch=1 regression ────────────────────────────────────────────────


class TestRegressionArch1:
    """Ensure arch=1 simulator still works."""

    def test_basic_mov_halt(self) -> None:
        cpu = run("MOV A, 42\nHLT", arch=1)
        assert cpu.a == 42
        assert cpu.state == CpuState.HALTED

    def test_fp_opcode_invalid_arch1(self) -> None:
        """FP opcode on arch=1 -> FAULT(INVALID_OPCODE)."""
        cpu = CPU(arch=1)
        cpu.load([142, 0x00, 0])  # FABS.F FA -- but arch=1
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.a == 6  # ERR_INVALID_OPCODE

    def test_no_fpu_on_arch1(self) -> None:
        """Arch=1 CPU has no FPU registers."""
        cpu = CPU(arch=1)
        assert cpu.regs.fpu is None

    def test_fpu_present_on_arch2(self) -> None:
        """Arch=2 CPU has FPU registers."""
        cpu = CPU(arch=2)
        assert cpu.regs.fpu is not None
