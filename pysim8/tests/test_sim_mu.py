"""Matrix Unit tests: unit (MuRegisters/MuQueue) + integration (CPU).

Coverage: register state → sync instructions → async issue/auto-inc →
arithmetic correctness → faults.
"""

from __future__ import annotations

import struct

import pytest
from conftest import run

from pysim8.isa import VU_FMT_F, VU_FMT_H, Op, encode_mfm, encode_vu_regs
from pysim8.sim.cpu import CPU
from pysim8.sim.errors import ErrorCode
from pysim8.sim.mu import MU_QUEUE_DEPTH, MuCommand, MuQueue, MuRegisters
from pysim8.sim.registers import CpuState

# ── Helpers ──────────────────────────────────────────────────────


def cpu3() -> CPU:
    return CPU(arch=3)


def load_run(cpu: CPU, code: list[int]) -> CpuState:
    cpu.load(code)
    return cpu.run()


def mset_imm(target: int, val: int) -> list[int]:
    """Encode MSET mreg, imm16."""
    return [188, target, val & 0xFF, (val >> 8) & 0xFF]


def mmul_bytes(
    fmt: int,
    dc: int,
    s1c: int,
    s2c: int,
    *,
    a_col: bool = False,
    b_col: bool = False,
    c_col: bool = False,
) -> list[int]:
    """Encode MMUL with given format and layout."""
    return [int(Op.MMUL), encode_mfm(fmt, a_col, b_col, c_col), encode_vu_regs(dc, s1c, s2c)]


def mmad_bytes(
    fmt: int,
    dc: int,
    s1c: int,
    s2c: int,
    *,
    a_col: bool = False,
    b_col: bool = False,
    c_col: bool = False,
) -> list[int]:
    """Encode MMAD with given format and layout."""
    return [int(Op.MMAD), encode_mfm(fmt, a_col, b_col, c_col), encode_vu_regs(dc, s1c, s2c)]


def write_f32_matrix(mem: object, base: int, values: list[float]) -> None:
    """Write FP32 values to memory starting at base (4 bytes each, little-endian)."""
    for i, v in enumerate(values):
        raw = struct.pack("<f", v)
        for j, b in enumerate(raw):
            mem[base + i * 4 + j] = b  # type: ignore[index]


def read_f32(mem: object, addr: int) -> float:
    raw = bytes(mem[addr + i] for i in range(4))  # type: ignore[index]
    return struct.unpack("<f", raw)[0]


def read_f32_matrix(mem: object, base: int, count: int) -> list[float]:
    return [read_f32(mem, base + i * 4) for i in range(count)]


def _mu_cmd(op: int = int(Op.MMUL)) -> MuCommand:
    return MuCommand(
        op=op,
        fmt=VU_FMT_F,
        a_col=False,
        b_col=False,
        c_col=False,
        accumulate=False,
        a_addr=0,
        b_addr=0,
        c_addr=0,
        m=1,
        n=1,
        k=1,
    )


# ── 1. MuRegisters unit tests ─────────────────────────────────────


class TestMuRegisters:
    def test_initial_all_zero(self) -> None:
        mu = MuRegisters()
        assert mu.ma == mu.mb == mu.mc == 0
        assert mu.mm == mu.mn == mu.mk == 0
        assert mu.mfpsr == 0

    def test_write_read_ptr_ma(self) -> None:
        mu = MuRegisters()
        mu.write_reg(0, 0x1234)
        assert mu.ma == 0x1234
        assert mu.read_ptr(0) == 0x1234

    def test_write_all_six_regs(self) -> None:
        mu = MuRegisters()
        for code, val in enumerate([0x100, 0x200, 0x300, 2, 4, 8]):
            mu.write_reg(code, val)
        assert (mu.ma, mu.mb, mu.mc) == (0x100, 0x200, 0x300)
        assert (mu.mm, mu.mn, mu.mk) == (2, 4, 8)

    def test_16bit_mask(self) -> None:
        mu = MuRegisters()
        mu.write_reg(0, 0x1FFFF)
        assert mu.ma == 0xFFFF

    def test_inc_ptr_normal(self) -> None:
        mu = MuRegisters()
        mu.write_reg(0, 0x0100)
        mu.inc_ptr(0, 64)
        assert mu.ma == 0x0140

    def test_inc_ptr_wraps_64k(self) -> None:
        mu = MuRegisters()
        mu.write_reg(0, 0xFFF0)
        mu.inc_ptr(0, 32)
        assert mu.ma == (0xFFF0 + 32) % 0x10000

    def test_reset_clears_all(self) -> None:
        mu = MuRegisters()
        for code in range(6):
            mu.write_reg(code, 0xABCD)
        mu.mfpsr = 0xFF
        mu.reset()
        assert mu.ma == mu.mb == mu.mc == 0
        assert mu.mm == mu.mn == mu.mk == 0
        assert mu.mfpsr == 0

    def test_invalid_ptr_code_raises(self) -> None:
        mu = MuRegisters()
        with pytest.raises(ValueError):
            mu.read_ptr(3)

    def test_invalid_reg_code_raises(self) -> None:
        mu = MuRegisters()
        with pytest.raises(ValueError):
            mu.write_reg(6, 0)


# ── 2. MuQueue unit tests ─────────────────────────────────────────


class TestMuQueue:
    def test_enqueue_dequeue_fifo(self) -> None:
        q = MuQueue()
        c1, c2 = _mu_cmd(int(Op.MMUL)), _mu_cmd(int(Op.MMUL))
        c1.m, c2.m = 1, 2
        q.enqueue(c1)
        q.enqueue(c2)
        assert len(q) == 2
        assert q.dequeue().m == 1
        assert q.dequeue().m == 2
        assert q.is_empty

    def test_full_raises(self) -> None:
        q = MuQueue()
        for _ in range(MU_QUEUE_DEPTH):
            q.enqueue(_mu_cmd())
        assert q.is_full
        with pytest.raises(RuntimeError):
            q.enqueue(_mu_cmd())

    def test_flush_clears(self) -> None:
        q = MuQueue()
        q.enqueue(_mu_cmd())
        q.flush()
        assert q.is_empty

    def test_fault_set_and_clear(self) -> None:
        q = MuQueue()
        q.fault = int(ErrorCode.VU_OOB)
        assert q.fault == int(ErrorCode.VU_OOB)
        q.reset()
        assert q.fault == 0 and q.is_empty

    def test_peek_does_not_consume(self) -> None:
        q = MuQueue()
        q.enqueue(_mu_cmd())
        _ = q.peek()
        assert len(q) == 1


# ── 3. MSET instruction tests ─────────────────────────────────────


class TestMSET:
    def test_mset_imm16_ma(self) -> None:
        cpu = cpu3()
        load_run(cpu, mset_imm(0, 0x0100) + [0])
        assert cpu._mu_regs.ma == 0x0100

    @pytest.mark.parametrize(
        "target,attr",
        [
            pytest.param(0, "ma", id="MA"),
            pytest.param(1, "mb", id="MB"),
            pytest.param(2, "mc", id="MC"),
            pytest.param(3, "mm", id="MM"),
            pytest.param(4, "mn", id="MN"),
            pytest.param(5, "mk", id="MK"),
        ],
    )
    def test_mset_imm16_all_targets(self, target: int, attr: str) -> None:
        cpu = cpu3()
        load_run(cpu, mset_imm(target, 42) + [0])
        assert getattr(cpu._mu_regs, attr) == 42

    def test_mset_imm16_full_16bit(self) -> None:
        cpu = cpu3()
        load_run(cpu, mset_imm(0, 0xABCD) + [0])
        assert cpu._mu_regs.ma == 0xABCD

    def test_mset_gpr_pair(self) -> None:
        cpu = cpu3()
        # MOV A, 1; MOV B, 2; MSET MA, B, A → MA = (2<<8)|1 = 0x0201
        code = [6, 0, 1, 6, 1, 2, 189, 0, (1 << 2) | 0, 0]
        load_run(cpu, code)
        assert cpu._mu_regs.ma == 0x0201

    def test_mset_gpr_single(self) -> None:
        cpu = cpu3()
        # MOV C, 7; MSET MA, C → MA = 7
        code = [6, 2, 7, 189, 0, 0x10 | 2, 0]
        load_run(cpu, code)
        assert cpu._mu_regs.ma == 7

    def test_mset_invalid_target_faults(self) -> None:
        cpu = cpu3()
        load_run(cpu, [188, 6, 0, 0, 0])  # target=6 → ERR_INVALID_REG
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.INVALID_REG

    def test_mset_asm_imm16(self) -> None:
        cpu = run("MSET MA, 0x0100\nHLT", arch=3)
        assert cpu._mu_regs.ma == 0x0100

    def test_mset_asm_gpr_pair(self) -> None:
        cpu = run("MOV A, 1\nMOV B, 2\nMSET MA, B, A\nHLT", arch=3)
        assert cpu._mu_regs.ma == 0x0201

    def test_mset_asm_single_gpr(self) -> None:
        cpu = run("MOV A, 99\nMSET MK, A\nHLT", arch=3)
        assert cpu._mu_regs.mk == 99


# ── 4. MFSTAT / MFCLR / MWAIT ────────────────────────────────────


class TestMuSync:
    def test_mfstat_copies_mfpsr_to_gpr(self) -> None:
        cpu = cpu3()
        code = [190, 0, 0]  # MFSTAT A; HLT
        cpu.load(code)
        cpu._mu_regs.mfpsr = 0x1F
        cpu.run()
        assert cpu.regs.a == 0x1F

    def test_mfstat_all_gpr_targets(self) -> None:
        for gpr in range(4):
            cpu = cpu3()
            code = [190, gpr, 0]
            cpu.load(code)
            cpu._mu_regs.mfpsr = 0x0A
            cpu.run()
            assert cpu.regs.read(gpr) == 0x0A

    def test_mfstat_invalid_gpr_faults(self) -> None:
        cpu = cpu3()
        load_run(cpu, [190, 4, 0])  # GPR=4 → ERR_INVALID_REG
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.INVALID_REG

    def test_mfclr_clears_mfpsr(self) -> None:
        cpu = cpu3()
        code = [191, 0]  # MFCLR; HLT
        cpu.load(code)
        cpu._mu_regs.mfpsr = 0xFF
        cpu.run()
        assert cpu._mu_regs.mfpsr == 0

    def test_mwait_empty_queue_halts(self) -> None:
        cpu = cpu3()
        state = load_run(cpu, [192, 0])  # MWAIT; HLT
        assert state == CpuState.HALTED

    def test_mwait_surfaces_deferred_fault(self) -> None:
        cpu = cpu3()
        code = [192, 0]  # MWAIT; HLT (unreachable)
        cpu.load(code)
        cpu._mu_queue.fault = int(ErrorCode.VU_OOB)
        cpu.run()
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_OOB

    def test_mwait_asm(self) -> None:
        cpu = run("MWAIT\nHLT", arch=3)
        assert cpu.state == CpuState.HALTED


# ── 5. MMUL basic arithmetic ─────────────────────────────────────


class TestMMUL:
    def _setup_2x2(self, cpu: CPU) -> None:
        """A=[[1,2],[3,4]], B=[[5,6],[7,8]] at 0x100/0x200; C at 0x300."""
        write_f32_matrix(cpu.mem, 0x100, [1.0, 2.0, 3.0, 4.0])
        write_f32_matrix(cpu.mem, 0x200, [5.0, 6.0, 7.0, 8.0])

    def test_1x1x1_scalar(self) -> None:
        cpu = cpu3()
        code = (
            mset_imm(0, 0x100)  # MA
            + mset_imm(1, 0x200)  # MB
            + mset_imm(2, 0x300)  # MC
            + mset_imm(3, 1)  # MM=1
            + mset_imm(4, 1)  # MN=1
            + mset_imm(5, 1)  # MK=1
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]  # MWAIT; HLT
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [3.0])
        write_f32_matrix(cpu.mem, 0x200, [4.0])
        cpu.run()
        assert read_f32(cpu.mem, 0x300) == pytest.approx(12.0)

    def test_2x2x2_result(self) -> None:
        cpu = cpu3()
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 2)  # MM=2
            + mset_imm(4, 2)  # MN=2
            + mset_imm(5, 2)  # MK=2
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        cpu.load(code)
        self._setup_2x2(cpu)
        cpu.run()
        result = read_f32_matrix(cpu.mem, 0x300, 4)
        assert result == pytest.approx([19.0, 22.0, 43.0, 50.0])

    def test_auto_increment_ma_mb_mc(self) -> None:
        cpu = cpu3()
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 2)
            + mset_imm(4, 2)
            + mset_imm(5, 2)
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        cpu.load(code)
        self._setup_2x2(cpu)
        cpu.run()
        mu = cpu._mu_regs
        # MA += M*K*sz = 2*2*4 = 16
        assert mu.ma == 0x100 + 16
        # MB += K*N*sz = 2*2*4 = 16
        assert mu.mb == 0x200 + 16
        # MC is NOT auto-incremented — stays put for K-loop accumulation.
        assert mu.mc == 0x300

    def test_auto_increment_deduplication_ma_in_both_src_roles(self) -> None:
        """MA used as both A-src and B-src: dedup picks the max stride."""
        cpu = cpu3()
        # M=1, N=2, K=1, sz=4 → A-role inc = 1*1*4 = 4, B-role inc = 1*2*4 = 8.
        # Dedup keeps max(4, 8) = 8.
        code = (
            mset_imm(0, 0x100)  # MA (used as both src1 and src2)
            + mset_imm(2, 0x300)  # MC
            + mset_imm(3, 1)
            + mset_imm(4, 2)
            + mset_imm(5, 1)
            + mmul_bytes(VU_FMT_F, 2, 0, 0)  # dc=MC=2, s1=MA=0, s2=MA=0
            + [192, 0]
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [1.0, 2.0])
        cpu.run()
        mu = cpu._mu_regs
        assert mu.ma == 0x108  # MA += max(4, 8) = 8
        assert mu.mc == 0x300  # MC has no auto-increment

    @pytest.mark.parametrize(
        "dim,val",
        [
            pytest.param("MM", 0, id="M=0"),
            pytest.param("MN", 0, id="N=0"),
            pytest.param("MK", 0, id="K=0"),
        ],
    )
    def test_noop_when_dim_is_zero(self, dim: str, val: int) -> None:
        cpu = cpu3()
        dims = {"MM": 2, "MN": 2, "MK": 2, dim: val}
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, dims["MM"])
            + mset_imm(4, dims["MN"])
            + mset_imm(5, dims["MK"])
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        cpu.load(code)
        cpu.run()
        assert cpu.state == CpuState.HALTED
        # No increment when degenerate
        mu = cpu._mu_regs
        assert mu.ma == 0x100
        assert mu.mb == 0x200
        assert mu.mc == 0x300

    def test_2x2x2_asm(self) -> None:
        cpu = run(
            "@page 1\n"
            "DB 0, 0, 0x80, 0x3F\n"  # [0x100] 1.0 F32 LE
            "DB 0, 0, 0,    0x40\n"  # [0x104] 2.0
            "DB 0, 0, 0x40, 0x40\n"  # [0x108] 3.0
            "DB 0, 0, 0x80, 0x40\n"  # [0x10C] 4.0
            "DB 0, 0, 0xA0, 0x40\n"  # [0x110] 5.0
            "DB 0, 0, 0xC0, 0x40\n"  # [0x114] 6.0
            "DB 0, 0, 0xE0, 0x40\n"  # [0x118] 7.0
            "DB 0, 0, 0,    0x41\n"  # [0x11C] 8.0
            "@page 0\n"
            "MSET MA, 0x0100\n"
            "MSET MB, 0x0110\n"
            "MSET MC, 0x0120\n"
            "MSET MM, 2\nMSET MN, 2\nMSET MK, 2\n"
            "MMUL.F MC, MA, MB\n"
            "MWAIT\nHLT",
            arch=3,
        )
        result = read_f32_matrix(cpu.mem, 0x0120, 4)
        assert result == pytest.approx([19.0, 22.0, 43.0, 50.0])


# ── 6. MMUL accumulate (.acc) ─────────────────────────────────────


class TestMMULAccumulate:
    def test_accumulate_adds_to_existing_c(self) -> None:
        cpu = cpu3()
        # A=[[1,2],[3,4]], B=[[5,6],[7,8]]
        # C_initial=[[10,0],[0,10]] (identity-ish)
        # C_result = C_initial + A@B = [[29,22],[43,60]]
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 2)
            + mset_imm(4, 2)
            + mset_imm(5, 2)
            + mmad_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [1.0, 2.0, 3.0, 4.0])
        write_f32_matrix(cpu.mem, 0x200, [5.0, 6.0, 7.0, 8.0])
        write_f32_matrix(cpu.mem, 0x300, [10.0, 0.0, 0.0, 10.0])
        cpu.run()
        result = read_f32_matrix(cpu.mem, 0x300, 4)
        assert result == pytest.approx([29.0, 22.0, 43.0, 60.0])

    def test_accumulate_asm_suffix(self) -> None:
        cpu = run(
            "MSET MA, 0x0100\nMSET MB, 0x0200\nMSET MC, 0x0300\n"
            "MSET MM, 1\nMSET MN, 1\nMSET MK, 1\n"
            "MMAD.F MC, MA, MB\nMWAIT\nHLT",
            arch=3,
        )
        # Verify instruction was accepted (CPU reached HALTED, not FAULT)
        assert cpu.state == CpuState.HALTED


# ── 7. MMUL layout modes ─────────────────────────────────────────


class TestMMULLayout:
    def test_b_col_layout(self) -> None:
        """B stored column-major (N×K); b_col=True gives same result as canonical K×N for identity A."""
        cpu = cpu3()
        # A = [[1.0, 0.0], [0.0, 1.0]] (identity, 2x2), row-major
        # B stored column-major N×K = [[5.0, 7.0], [6.0, 8.0]] at 0x200
        # Represents B = [[5,6],[7,8]] (row-major K×N)
        # C = I @ B = B = [[5,6],[7,8]]
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 2)
            + mset_imm(4, 2)
            + mset_imm(5, 2)
            + mmul_bytes(VU_FMT_F, 2, 0, 1, b_col=True)
            + [192, 0]
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [1.0, 0.0, 0.0, 1.0])
        write_f32_matrix(cpu.mem, 0x200, [5.0, 7.0, 6.0, 8.0])  # stored column-major
        cpu.run()
        result = read_f32_matrix(cpu.mem, 0x300, 4)
        assert result == pytest.approx([5.0, 6.0, 7.0, 8.0])

    def test_b_col_asm_suffix(self) -> None:
        cpu = run(
            "MSET MA, 0x0100\nMSET MB, 0x0200\nMSET MC, 0x0300\n"
            "MSET MM, 1\nMSET MN, 1\nMSET MK, 1\n"
            "MMUL.F.rcr MC, MA, MB\nMWAIT\nHLT",
            arch=3,
        )
        assert cpu.state == CpuState.HALTED

    def test_a_col_layout(self) -> None:
        """A stored column-major (bit5 of mfm): valid, no fault."""
        cpu = cpu3()
        # A = [[1.0], [2.0]] stored column-major at 0x100 (K×M = 1×2)
        # B = [[3.0]] at 0x200 (1×1)
        # C = A(col) @ B = [[1*3], [2*3]] = [[3], [6]] at 0x300
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 2)  # M=2
            + mset_imm(4, 1)  # N=1
            + mset_imm(5, 1)  # K=1
            + mmul_bytes(VU_FMT_F, 2, 0, 1, a_col=True)
            + [192, 0]
        )
        cpu.load(code)
        # A column-major M×K=2×1: [A[0,0], A[1,0]] = [1.0, 2.0]
        write_f32_matrix(cpu.mem, 0x100, [1.0, 2.0])
        write_f32_matrix(cpu.mem, 0x200, [3.0])
        cpu.run()
        assert cpu.state == CpuState.HALTED
        result = read_f32_matrix(cpu.mem, 0x300, 2)
        assert result == pytest.approx([3.0, 6.0])

    def test_c_col_layout(self) -> None:
        """C stored column-major (bit3 of mfm): result written in column-major order."""
        cpu = cpu3()
        # A = [[1.0, 2.0]], B = [[3.0], [4.0]], C = [[1*3+2*4]] = [[11.0]]
        # M=1, N=1, K=2 — trivial 1x1 output, layout doesn't matter for 1x1
        # Use M=2, N=2, K=1: A=[[1,2]], B=[[3],[4]], C(c_col) = column-major
        # A M×K=2×1 row-major: [1.0, 2.0], B K×N=1×2 row-major: [3.0, 4.0]
        # C[0,0]=1*3=3, C[0,1]=1*4=4, C[1,0]=2*3=6, C[1,1]=2*4=8
        # c_col: written as [C[0,0],C[1,0],C[0,1],C[1,1]] = [3,6,4,8]
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 2)  # M=2
            + mset_imm(4, 2)  # N=2
            + mset_imm(5, 1)  # K=1
            + mmul_bytes(VU_FMT_F, 2, 0, 1, c_col=True)
            + [192, 0]
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [1.0, 2.0])  # A 2×1 row-major
        write_f32_matrix(cpu.mem, 0x200, [3.0, 4.0])  # B 1×2 row-major
        cpu.run()
        assert cpu.state == CpuState.HALTED
        result = read_f32_matrix(cpu.mem, 0x300, 4)
        # column-major: C[0,0]=3, C[1,0]=6, C[0,1]=4, C[1,1]=8
        assert result == pytest.approx([3.0, 6.0, 4.0, 8.0])


# ── 8. MFPSR accumulation via MMUL ───────────────────────────────


class TestMFPSR:
    def test_mfpsr_accumulates_fp_flags(self) -> None:
        """MMUL with overflow-producing values sets MFPSR bits."""
        cpu = cpu3()
        # Very large values → overflow on multiply
        huge = 1e38
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 1)
            + mset_imm(4, 1)
            + mset_imm(5, 1)
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [huge])
        write_f32_matrix(cpu.mem, 0x200, [huge])
        cpu.run()
        assert cpu._mu_regs.mfpsr != 0, "Expected FP exception flags after overflow"

    def test_mfclr_after_mwait_clears_flags(self) -> None:
        cpu = cpu3()
        huge = 1e38
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 1)
            + mset_imm(4, 1)
            + mset_imm(5, 1)
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192]  # MWAIT
            + [191]  # MFCLR
            + [0]  # HLT
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [huge])
        write_f32_matrix(cpu.mem, 0x200, [huge])
        cpu.run()
        assert cpu._mu_regs.mfpsr == 0


# ── 9. Multiple queued commands ───────────────────────────────────


class TestMMULChained:
    def test_two_sequential_mmuls(self) -> None:
        """Issue two MMUL commands; MWAIT drains both.
        MA / MB advance via auto-increment; MC must be re-MSET to land
        the second result at a new address (MC has no auto-inc)."""
        cpu = cpu3()
        # A1 = [[2.0]], B1 = [[3.0]] → C1 = [[6.0]]
        # A2 = [[4.0]], B2 = [[5.0]] → C2 = [[20.0]]
        code = (
            # First MMUL
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 1)
            + mset_imm(4, 1)
            + mset_imm(5, 1)
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            # Second MMUL: MA / MB auto-incremented to 0x104 / 0x204;
            # explicitly point MC at 0x304 since MC does not auto-increment.
            + mset_imm(2, 0x304)
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]  # MWAIT; HLT
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [2.0])  # A1
        write_f32_matrix(cpu.mem, 0x104, [4.0])  # A2 (MA after first auto-inc)
        write_f32_matrix(cpu.mem, 0x200, [3.0])  # B1
        write_f32_matrix(cpu.mem, 0x204, [5.0])  # B2 (MB after first auto-inc)
        cpu.run()
        assert cpu.state == CpuState.HALTED
        assert read_f32(cpu.mem, 0x300) == pytest.approx(6.0)
        assert read_f32(cpu.mem, 0x304) == pytest.approx(20.0)


# ── 10. Fault tests ───────────────────────────────────────────────


class TestMuFaults:
    @pytest.mark.parametrize(
        "mfm,regs,desc",
        [
            pytest.param(0xC0, 0x08, "mfm_bits76_set", id="mfm_reserved_bits"),
            pytest.param(0x07, 0x08, "fmt_code_7", id="fmt_code_7"),
            pytest.param(0x00, 0x0B, "regs_bits10_set", id="regs_reserved_bits"),
            pytest.param(0x00, 0x0C, "src2_code_3", id="src2_reg_code_3"),
        ],
    )
    def test_mmul_format_fault(self, mfm: int, regs: int, desc: str) -> None:
        cpu = cpu3()
        code = mset_imm(3, 1) + mset_imm(4, 1) + mset_imm(5, 1) + [int(Op.MMUL), mfm, regs] + [0]
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT

    def test_mmul_oob_a_deferred(self) -> None:
        """A extent past 64 KB → ERR_VU_OOB surfaced at MWAIT."""
        cpu = cpu3()
        # MA=0xFF00, M=1, K=65 → A extent = 0xFF00 + 1*65*4 = 65540 > 65536
        code = (
            mset_imm(0, 0xFF00)  # MA = 0xFF00
            + mset_imm(1, 0x0200)
            + mset_imm(2, 0x0300)
            + mset_imm(3, 1)  # M=1
            + mset_imm(4, 1)
            + mset_imm(5, 65)  # K=65 → A extent overflows
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_OOB

    def test_mmul_oob_b_deferred(self) -> None:
        """B extent past 64 KB → ERR_VU_OOB surfaced at MWAIT."""
        cpu = cpu3()
        # MB=0xFF00, K=65, N=1 → B extent = 0xFF00 + 65*1*4 = 65540 > 65536
        code = (
            mset_imm(0, 0x0100)
            + mset_imm(1, 0xFF00)  # MB near end
            + mset_imm(2, 0x0300)
            + mset_imm(3, 1)
            + mset_imm(4, 1)  # N=1
            + mset_imm(5, 65)  # K=65 → B extent overflows
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_OOB

    def test_mset_invalid_target_faults(self) -> None:
        cpu = cpu3()
        load_run(cpu, [188, 6, 0, 0, 0])
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.INVALID_REG

    def test_mfstat_invalid_gpr_faults(self) -> None:
        cpu = cpu3()
        load_run(cpu, [190, 5, 0])  # GPR=5 → ERR_INVALID_REG
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.INVALID_REG

    def test_mmul_oob_c_deferred(self) -> None:
        """C extent past 64 KB → ERR_VU_OOB surfaced at MWAIT."""
        cpu = cpu3()
        # MC=0xFF00, M=65, N=1 → C extent = 0xFF00 + 65*1*4 = 65540 > 65536
        code = (
            mset_imm(0, 0x0100)
            + mset_imm(1, 0x0200)
            + mset_imm(2, 0xFF00)  # MC near end
            + mset_imm(3, 65)  # M=65 → C extent overflows
            + mset_imm(4, 1)  # N=1
            + mset_imm(5, 1)
            + mmul_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_OOB


# ── 11. MMAD tests ────────────────────────────────────────────────


class TestMMAD:
    def test_mmad_accumulates(self) -> None:
        cpu = cpu3()
        code = (
            mset_imm(0, 0x100)
            + mset_imm(1, 0x200)
            + mset_imm(2, 0x300)
            + mset_imm(3, 1)
            + mset_imm(4, 1)
            + mset_imm(5, 1)
            + mmad_bytes(VU_FMT_F, 2, 0, 1)
            + [192, 0]
        )
        cpu.load(code)
        write_f32_matrix(cpu.mem, 0x100, [3.0])
        write_f32_matrix(cpu.mem, 0x200, [4.0])
        write_f32_matrix(cpu.mem, 0x300, [10.0])  # initial C
        cpu.run()
        assert cpu.state == CpuState.HALTED
        assert read_f32(cpu.mem, 0x300) == pytest.approx(22.0)  # 10 + 3*4

    def test_mmad_asm(self) -> None:
        cpu = run(
            "MSET MA, 0x0100\nMSET MB, 0x0200\nMSET MC, 0x0300\n"
            "MSET MM, 1\nMSET MN, 1\nMSET MK, 1\n"
            "MMAD.F MC, MA, MB\nMWAIT\nHLT",
            arch=3,
        )
        assert cpu.state == CpuState.HALTED
