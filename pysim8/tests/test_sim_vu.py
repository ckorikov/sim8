"""Vector Unit tests — unit (fake VU) and integration (real VU).

Tests are organized TDD-style: basic register ops → sync instructions →
async issue/queue → element arithmetic → auto-increment → faults.
"""

from __future__ import annotations

import pytest
from conftest import asm_bytes, asm_error, run

from pysim8.isa import (
    VU_CMP_SUFFIX,
    VU_FMT_U,
    VU_MODE_R,
    VU_MODE_VS,
    VU_MODE_VV,
    Op,
    encode_vfm,
    encode_vu_regs,
)
from pysim8.sim.cpu import CPU
from pysim8.sim.errors import ErrorCode
from pysim8.sim.registers import CpuState
from pysim8.sim.vu import VuCommand, VuQueue, VuRegisters

# ── Helpers ──────────────────────────────────────────────────────


def cpu3() -> CPU:
    """Create a fresh arch=3 CPU."""
    return CPU(arch=3)


def load_run(cpu: CPU, code: list[int]) -> CpuState:
    """Load bytecode and run to completion."""
    cpu.load(code)
    return cpu.run()


def vset_imm16(target: int, val: int) -> list[int]:
    """Encode VSET reg, #imm16."""
    return [163, target, val & 0xFF, (val >> 8) & 0xFF]


def vasync(op: int, fmt: int, mode: int, dst: int, s1: int, s2: int, cond: int = 0) -> list[int]:
    """Encode async VU instruction (base 3 bytes; VCMP appends cond as 4th byte)."""
    result = [op, encode_vfm(fmt, mode), encode_vu_regs(dst, s1, s2)]
    if op == int(Op.VCMP):
        result.append(cond)
    return result


# ── 1. VuRegisters unit tests ───────────────────────────────────


class TestVuRegisters:
    def test_initial_state(self) -> None:
        vu = VuRegisters()
        assert vu.va == vu.vb == vu.vc == vu.vm == vu.vl == vu.vfpsr == 0

    def test_write_read_ptr(self) -> None:
        vu = VuRegisters()
        vu.write_reg(0, 0x1234)
        assert vu.va == 0x1234
        assert vu.read_ptr(0) == 0x1234

    def test_write_vl(self) -> None:
        vu = VuRegisters()
        vu.write_reg(4, 1000)
        assert vu.vl == 1000

    def test_16bit_mask(self) -> None:
        vu = VuRegisters()
        vu.write_reg(0, 0x1FFFF)
        assert vu.va == 0xFFFF

    def test_inc_ptr_wraps(self) -> None:
        vu = VuRegisters()
        vu.write_reg(0, 0xFFFE)
        vu.inc_ptr(0, 4)
        assert vu.va == 2  # 0xFFFE + 4 = 0x10002 → 2

    def test_reset(self) -> None:
        vu = VuRegisters()
        vu.write_reg(0, 0x1234)
        vu.vfpsr = 0xFF
        vu.reset()
        assert vu.va == 0 and vu.vfpsr == 0

    def test_invalid_ptr_code_raises(self) -> None:
        vu = VuRegisters()
        with pytest.raises(ValueError):
            vu.read_ptr(5)

    def test_invalid_reg_code_raises(self) -> None:
        vu = VuRegisters()
        with pytest.raises(ValueError):
            vu.write_reg(6, 0)


# ── 2. VuQueue unit tests ───────────────────────────────────────


class TestVuQueue:
    def _cmd(self, op: int = 170) -> VuCommand:
        return VuCommand(op=op, fmt=5, mode=0, cond=0, dst_addr=0, s1_addr=0, s2_addr=0, mask_addr=0, vl=4, imm=0)

    def test_enqueue_dequeue(self) -> None:
        q = VuQueue()
        q.enqueue(self._cmd(170))
        q.enqueue(self._cmd(171))
        assert len(q) == 2
        assert q.dequeue().op == 170
        assert q.dequeue().op == 171
        assert q.is_empty

    def test_full_raises(self) -> None:
        q = VuQueue()
        for _ in range(4):
            q.enqueue(self._cmd())
        assert q.is_full
        with pytest.raises(RuntimeError):
            q.enqueue(self._cmd())

    def test_flush(self) -> None:
        q = VuQueue()
        q.enqueue(self._cmd())
        q.flush()
        assert q.is_empty

    def test_fault_state(self) -> None:
        q = VuQueue()
        q.fault = 13
        assert q.fault == 13
        q.reset()
        assert q.fault == 0


# ── 3. VSET sync instruction tests ──────────────────────────────


class TestVSET:
    def test_vset_imm16_va(self) -> None:
        cpu = cpu3()
        load_run(cpu, vset_imm16(0, 0x0200) + [0])
        assert cpu.regs.vu.va == 0x0200

    def test_vset_imm16_vl(self) -> None:
        cpu = cpu3()
        load_run(cpu, vset_imm16(4, 100) + [0])
        assert cpu.regs.vu.vl == 100

    def test_vset_all_regs(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0x0100)
            + vset_imm16(1, 0x0200)
            + vset_imm16(2, 0x0300)
            + vset_imm16(3, 0x0400)
            + vset_imm16(4, 50)
            + [0]
        )
        load_run(cpu, code)
        vu = cpu.regs.vu
        assert (vu.va, vu.vb, vu.vc, vu.vm, vu.vl) == (0x0100, 0x0200, 0x0300, 0x0400, 50)

    def test_vset_invalid_target_faults(self) -> None:
        cpu = cpu3()
        code = [163, 5, 0, 0, 0]  # target=5 → ERR_INVALID_REG
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.INVALID_REG

    def test_vset_gpr_pair(self) -> None:
        cpu = cpu3()
        # MOV A, 1; MOV B, 0x50; VSET VA, A, B; HLT
        code = [6, 0, 1, 6, 1, 0x50, 164, 0, (0 << 2) | 1, 0]
        load_run(cpu, code)
        assert cpu.regs.vu.va == 0x0150

    def test_vset_single_gpr(self) -> None:
        cpu = cpu3()
        # MOV A, 42; VSET VL, A; HLT
        code = [6, 0, 42, 164, 4, 0x10, 0]
        load_run(cpu, code)
        assert cpu.regs.vu.vl == 42

    def test_vset_single_gpr_b(self) -> None:
        cpu = cpu3()
        # MOV B, 200; VSET VL, B; HLT
        code = [6, 1, 200, 164, 4, 0x11, 0]
        load_run(cpu, code)
        assert cpu.regs.vu.vl == 200


# ── 4. VFSTAT / VFCLR / VWAIT ───────────────────────────────────


class TestVuSync:
    def test_vfstat_reads_vfpsr(self) -> None:
        cpu = cpu3()
        code = [167, 0, 0]  # VFSTAT A; HLT
        cpu.load(code)
        cpu.regs.vu.vfpsr = 0x15  # set after load (load resets)
        cpu.run()
        assert cpu.regs.a == 0x15

    def test_vfclr_clears_vfpsr(self) -> None:
        cpu = cpu3()
        code = [168, 0]  # VFCLR; HLT
        cpu.load(code)
        cpu.regs.vu.vfpsr = 0xFF
        cpu.run()
        assert cpu.regs.vu.vfpsr == 0

    def test_vwait_no_fault(self) -> None:
        cpu = cpu3()
        code = [169, 0]  # VWAIT; HLT
        state = load_run(cpu, code)
        assert state == CpuState.HALTED


# ── 5. Async: VADD.U.vv integration ─────────────────────────────


class TestVAddU:
    def _setup_vadd_u_vv(self, cpu: CPU) -> None:
        """Set up memory and registers for VADD.U.vv test."""
        for i, v in enumerate([10, 20, 30, 40]):
            cpu.mem[0x0100 + i] = v
        for i, v in enumerate([1, 2, 3, 4]):
            cpu.mem[0x0110 + i] = v

    def test_vadd_u_vv_bytecode(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0x0100)  # VA
            + vset_imm16(1, 0x0110)  # VB
            + vset_imm16(2, 0x0120)  # VC
            + vset_imm16(4, 4)  # VL=4
            + vasync(int(Op.VADD), VU_FMT_U, VU_MODE_VV, 2, 0, 1)
            + [169, 0]  # VWAIT; HLT
        )
        cpu.load(code)
        self._setup_vadd_u_vv(cpu)
        cpu.run()
        assert [cpu.mem[0x0120 + i] for i in range(4)] == [11, 22, 33, 44]

    def test_vadd_u_vv_auto_increment(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0x0100)
            + vset_imm16(1, 0x0110)
            + vset_imm16(2, 0x0120)
            + vset_imm16(4, 4)
            + vasync(int(Op.VADD), VU_FMT_U, VU_MODE_VV, 2, 0, 1)
            + [169, 0]
        )
        cpu.load(code)
        self._setup_vadd_u_vv(cpu)
        cpu.run()
        vu = cpu.regs.vu
        assert vu.va == 0x0104
        assert vu.vb == 0x0114
        assert vu.vc == 0x0124

    def test_vadd_u_vv_vl_zero_noop(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0x0100)
            + vset_imm16(4, 0)  # VL=0
            + vasync(int(Op.VADD), VU_FMT_U, VU_MODE_VV, 0, 0, 1)
            + [169, 0]
        )
        cpu.load(code)
        cpu.run()
        assert cpu.regs.vu.va == 0x0100  # no increment

    def test_vadd_u_wrapping(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0x0100)
            + vset_imm16(1, 0x0110)
            + vset_imm16(2, 0x0120)
            + vset_imm16(4, 1)
            + vasync(int(Op.VADD), VU_FMT_U, VU_MODE_VV, 2, 0, 1)
            + [169, 0]
        )
        cpu.load(code)
        cpu.mem[0x0100] = 200
        cpu.mem[0x0110] = 100
        cpu.run()
        assert cpu.mem[0x0120] == 44  # (200 + 100) mod 256

    def test_vadd_u_assembler(self) -> None:
        cpu = run(
            "@page 1\n"
            "src1: DB 10, 20, 30, 40\n"
            "src2: DB 1, 2, 3, 4\n"
            "@page 0\n"
            "VSET VA, {src1}, src1\nVSET VB, {src2}, src2\nVSET VC, 0x0120\nVSET VL, 4\n"
            "VADD.U.vv VC, VA, VB\nVWAIT\nHLT",
            arch=3,
        )
        assert [cpu.mem[0x0120 + i] for i in range(4)] == [11, 22, 33, 44]


# ── 6. Reduction mode (.r) ──────────────────────────────────────


class TestReduction:
    def test_vadd_u_reduction(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0x0100)  # VA (src)
            + vset_imm16(2, 0x0120)  # VC (dst)
            + vset_imm16(4, 4)
            + vasync(int(Op.VADD), VU_FMT_U, VU_MODE_R, 2, 0, 0)
            + [169, 0]
        )
        cpu.load(code)
        for i, v in enumerate([10, 20, 30, 40]):
            cpu.mem[0x0100 + i] = v
        cpu.run()
        assert cpu.mem[0x0120] == 100  # 10+20+30+40

    def test_reduction_dst_increments_by_s(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0x0100)
            + vset_imm16(2, 0x0120)
            + vset_imm16(4, 4)
            + vasync(int(Op.VADD), VU_FMT_U, VU_MODE_R, 2, 0, 0)
            + [169, 0]
        )
        cpu.load(code)
        for i in range(4):
            cpu.mem[0x0100 + i] = 1
        cpu.run()
        # dst increments by s (1 byte for U), not S (4 bytes)
        assert cpu.regs.vu.vc == 0x0121


# ── 7. Fault tests ──────────────────────────────────────────────


class TestVuFaults:
    def test_invalid_vfm_fmt7_faults(self) -> None:
        cpu = cpu3()
        vfm_enc = encode_vfm(7, VU_MODE_VV)  # fmt=7 → reserved
        code = vset_imm16(4, 4) + [int(Op.VADD), vfm_enc, 0, 0]
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT

    def test_vdot_int_faults(self) -> None:
        cpu = cpu3()
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)
        code = (
            vset_imm16(0, 0x0100)
            + vset_imm16(1, 0x0110)
            + vset_imm16(2, 0x0120)
            + vset_imm16(4, 4)
            + [int(Op.VDOT), vfm_enc, encode_vu_regs(2, 0, 1), 0]
        )
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT

    def test_oob_faults_at_vwait(self) -> None:
        cpu = cpu3()
        code = (
            vset_imm16(0, 0xFFFC)  # VA near end of memory
            + vset_imm16(1, 0x0100)
            + vset_imm16(2, 0x0200)
            + vset_imm16(4, 8)  # VL=8, 8 bytes > 4 remaining
            + vasync(int(Op.VADD), VU_FMT_U, VU_MODE_VV, 2, 0, 1)
            + [169, 0]
        )
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_OOB

    def test_invalid_mode_for_vdot_faults(self) -> None:
        """VDOT only supports .vv (mode=0). Mode=1 (.vs) should FAULT."""
        cpu = cpu3()
        vfm_enc = encode_vfm(0, VU_MODE_VS)  # float32, .vs — invalid for VDOT
        code = (
            vset_imm16(0, 0x0100)
            + vset_imm16(1, 0x0110)
            + vset_imm16(2, 0x0120)
            + vset_imm16(4, 4)
            + [int(Op.VDOT), vfm_enc, encode_vu_regs(2, 0, 1), 0]
        )
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT

    def test_reserved_regs_bits_fault(self) -> None:
        cpu = cpu3()
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)
        regs_byte = encode_vu_regs(2, 0, 1) | 0x01  # bit[0] set
        code = vset_imm16(4, 4) + [int(Op.VADD), vfm_enc, regs_byte, 0]
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT


# ── 8. Assembler tests ──────────────────────────────────────────


class TestVuAssembler:
    def test_vset_encoding(self) -> None:
        code = asm_bytes("VSET VA, 0x0100\nHLT", arch=3)
        assert code == [163, 0, 0, 1, 0]

    def test_vset_composite_bytes(self) -> None:
        # VSET VA, hi, lo → [VSET_IMM16, 0, lo, hi]
        code = asm_bytes("VSET VA, 0x01, 0x20\nHLT", arch=3)
        assert code == [163, 0, 0x20, 0x01, 0]

    def test_vset_composite_hi_out_of_range(self) -> None:
        asm_error("VSET VA, 256, 0\nHLT", arch=3)

    def test_vset_composite_lo_out_of_range(self) -> None:
        asm_error("VSET VA, 0, 256\nHLT", arch=3)

    def test_vadd_encoding(self) -> None:
        code = asm_bytes("VADD.U.vv VC, VA, VB\nHLT", arch=3)
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)
        regs = encode_vu_regs(2, 0, 1)
        assert code == [int(Op.VADD), vfm_enc, regs, 0]

    def test_vfclr_encoding(self) -> None:
        code = asm_bytes("VFCLR\nHLT", arch=3)
        assert code == [168, 0]

    def test_vwait_encoding(self) -> None:
        code = asm_bytes("VWAIT\nHLT", arch=3)
        assert code == [169, 0]

    def test_vcmp_condition_suffix(self) -> None:
        code = asm_bytes("VCMP.U.LT VM, VA, VB\nHLT", arch=3)
        vfm_enc = encode_vfm(VU_FMT_U, 0)  # mode=0(vv), cond now in 4th byte
        regs = encode_vu_regs(3, 0, 1)  # dst=VM, s1=VA, s2=VB
        cond = VU_CMP_SUFFIX["LT"]  # cond=2
        assert code == [int(Op.VCMP), vfm_enc, regs, cond, 0]

    def test_vu_regs_not_labels_in_arch2(self) -> None:
        # VA should not be recognized as VU register in arch=2
        code = asm_bytes("va: JMP va\nHLT", arch=2)
        assert len(code) > 0  # should compile as label, not VU reg

    def test_vset_label_resolves_16bit(self) -> None:
        cpu = run(
            "@page 2\ndata: DB 42\n@page 0\nVSET VA, {data}, data\nHLT",
            arch=3,
        )
        assert cpu.regs.vu.va == 0x0200  # page 2, offset 0

    def test_vset_label_full_address(self) -> None:
        # VSET VA, label → full 16-bit: hi=page(label), lo=offset(label)
        cpu = run(
            "@page 2\ndata: DB 1, 2, 3\n@page 0\nVSET VA, data\nHLT",
            arch=3,
        )
        assert cpu.regs.vu.va == 0x0200  # page 2, offset 0

    def test_vset_label_page0_address(self) -> None:
        cpu = run("JMP start\ndata: DB 1, 2, 3\nstart: VSET VA, data\nHLT", arch=3)
        assert cpu.regs.vu.va == 2  # page 0, offset 2

    def test_vset_label_encoding(self) -> None:
        code = asm_bytes("data: DB 0\nVSET VA, data\nHLT", arch=3)
        # [163, 0(VA), lo=0(offset), hi=0(page)]
        assert code[1:5] == [163, 0, 0, 0]

    def test_vset_invalid_format_suffix_fails(self) -> None:
        asm_error("VADD.X.vv VC, VA, VB\nHLT", arch=3)


# ── 9. VEXP / VFMADD / VMOV broadcast — end-to-end ───────────────


def _bf16_at(cpu: CPU, addr: int) -> float:
    import struct as _struct

    raw = (cpu.mem[addr + 1] << 8) | cpu.mem[addr]
    return _struct.unpack("<f", _struct.pack("<I", raw << 16))[0]


def _f32_at(cpu: CPU, addr: int) -> float:
    import struct as _struct

    return _struct.unpack("<f", bytes(cpu.mem[addr + i] for i in range(4)))[0]


class TestVuExp:
    def test_exp_bf16_basic(self) -> None:
        import math as _math

        src = (
            "@page 1\nbuf: DB 0.0_bf, 1.0_bf, 2.0_bf, -1.0_bf\n"
            "@page 0\n"
            "VSET VL, 4\nVSET VA, buf\nVSET VC, buf\nVEXP.BF VC, VA\nVWAIT\nHLT\n"
        )
        cpu = run(src, arch=3)
        assert cpu.state == CpuState.HALTED
        for i, expected in enumerate([1.0, _math.e, _math.exp(2), _math.exp(-1)]):
            actual = _bf16_at(cpu, 256 + i * 2)
            assert abs(actual - expected) / max(expected, 1e-9) < 0.05

    def test_exp_integer_format_faults(self) -> None:
        cpu = cpu3()
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)
        code = vset_imm16(4, 4) + [int(Op.VEXP), vfm_enc, encode_vu_regs(2, 0, 0), 0]
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT

    def test_exp_unary_only_vv_mode(self) -> None:
        # VEXP in VS mode → FAULT
        cpu = cpu3()
        vfm_enc = encode_vfm(0, VU_MODE_VS)  # fmt=F, mode=vs
        code = vset_imm16(4, 4) + [int(Op.VEXP), vfm_enc, encode_vu_regs(2, 0, 0), 0]
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT

    def test_exp_assembler_emits_unary(self) -> None:
        code = asm_bytes(
            "@page 1\nbuf: DB 1.0_bf, 2.0_bf\n@page 0\nVSET VL, 2\nVSET VA, buf\nVSET VC, buf\nVEXP.BF VC, VA\nHLT\n",
            arch=3,
        )
        # Find VEXP opcode in code stream
        assert int(Op.VEXP) in code


class TestVuFmadd:
    def test_fmadd_f32_vv(self) -> None:
        src = (
            "@page 1\n"
            "va_buf: DB 1.0_f, 2.0_f, 3.0_f, 4.0_f\n"
            "vb_buf: DB 5.0_f, 6.0_f, 7.0_f, 8.0_f\n"
            "vc_buf: DB 0.5_f, 1.0_f, 1.5_f, 2.0_f\n"
            "@page 0\n"
            "VSET VL, 4\n"
            "VSET VA, va_buf\nVSET VB, vb_buf\nVSET VC, vc_buf\n"
            "VFMADD.F VC, VA, VB\nVWAIT\nHLT\n"
        )
        cpu = run(src, arch=3)
        assert cpu.state == CpuState.HALTED
        # vc_buf is at offset 32 in page 1 (after va=16 + vb=16)
        for i, exp in enumerate([5.5, 13.0, 22.5, 34.0]):
            assert abs(_f32_at(cpu, 256 + 32 + i * 4) - exp) < 1e-5

    def test_fmadd_bf16_vs_mem_broadcast(self) -> None:
        """VFMADD vs mode: dst[i] += src1[i] * mem[s2_ptr] (bf16 scalar from memory)."""
        # Layout (page 1):
        #   0..7   va_buf: bf16 [1.0, 2.0, 4.0, 8.0]
        #   8..15  vc_buf: bf16 [0, 0, 0, 0]
        #   16..17 scal:   bf16 2.0
        src = (
            "@page 1\n"
            "va_buf: DB 1.0_bf, 2.0_bf, 4.0_bf, 8.0_bf\n"
            "vc_buf: DB 0.0_bf, 0.0_bf, 0.0_bf, 0.0_bf\n"
            "scal:   DB 2.0_bf\n"
            "@page 0\n"
            "VSET VL, 4\n"
            "VSET VA, va_buf\n"
            "VSET VB, scal\n"
            "VSET VC, vc_buf\n"
            "VFMADD.BF.vs VC, VA, VB\n"
            "VWAIT\nHLT\n"
        )
        cpu = run(src, arch=3)
        assert cpu.state == CpuState.HALTED
        from pysim8.fp_formats import bytes_to_float

        for i, expected in enumerate([2.0, 4.0, 8.0, 16.0]):
            val = bytes_to_float(bytes(cpu.mem[264 + i * 2 + j] for j in range(2)), 2)  # fmt=BF=2
            assert abs(val - expected) < 0.05

    def test_fmadd_integer_format_faults(self) -> None:
        cpu = cpu3()
        vfm_enc = encode_vfm(VU_FMT_U, VU_MODE_VV)
        code = vset_imm16(4, 4) + [int(Op.VFMADD), vfm_enc, encode_vu_regs(2, 0, 1), 0]
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT

    def test_fmadd_no_reduction_mode(self) -> None:
        # VFMADD with mode=R should fault (no reduction semantics defined)
        cpu = cpu3()
        vfm_enc = encode_vfm(0, VU_MODE_R)  # fmt=F, mode=R
        code = vset_imm16(4, 4) + [int(Op.VFMADD), vfm_enc, encode_vu_regs(2, 0, 0), 0]
        load_run(cpu, code)
        assert cpu.state == CpuState.FAULT
        assert cpu.regs.a == ErrorCode.VU_FORMAT


class TestVMovBroadcast:
    def test_vmov_vs_mem_broadcast_byte(self) -> None:
        """VMOV.U.vs VC, VB — read 1 byte from mem[VB], broadcast to VL elements."""
        src = (
            "@page 1\n"
            "scal: DB 0x77\n"
            "@page 1, 4\n"
            "buf:  DB 0xAA, 0xBB, 0xCC, 0xDD\n"
            "@page 0\n"
            "VSET VL, 4\nVSET VB, scal\nVSET VC, buf\n"
            "VMOV.U.vs VC, VB\nVWAIT\nHLT\n"
        )
        cpu = run(src, arch=3)
        assert cpu.state == CpuState.HALTED
        assert list(cpu.mem[260:264]) == [0x77] * 4
        # VB does NOT auto-advance in vs mode (snapshot once, reusable)
        assert cpu.regs.vu.vb == 256

    def test_vmov_vs_mem_broadcast_bf16(self) -> None:
        """VMOV.BF.vs VC, VB — bf16 scalar broadcast (multi-byte FP)."""
        src = (
            "@page 1\n"
            "scal: DB 1.5_bf\n"
            "@page 1, 8\n"
            "buf:  DB 0, 0, 0, 0, 0, 0, 0, 0\n"
            "@page 0\n"
            "VSET VL, 4\nVSET VB, scal\nVSET VC, buf\n"
            "VMOV.BF.vs VC, VB\nVWAIT\nHLT\n"
        )
        cpu = run(src, arch=3)
        assert cpu.state == CpuState.HALTED
        # bf16(1.5) = 0x3FC0 (LE: 0xC0 0x3F)
        for i in range(4):
            assert cpu.mem[264 + i * 2] == 0xC0
            assert cpu.mem[264 + i * 2 + 1] == 0x3F
        # VC advanced by 8 (4 elems × 2B), VB unchanged
        assert cpu.regs.vu.vb == 256
        assert cpu.regs.vu.vc == 264 + 8

    def test_vmov_vi_imm_broadcast(self) -> None:
        """VMOV vi mode broadcasts immediate."""
        src = (
            "@page 1\nbuf: DB 0xAA, 0xBB, 0xCC, 0xDD\n@page 0\nVSET VL, 4\nVSET VC, buf\nVMOV.U VC, 0x55\nVWAIT\nHLT\n"
        )
        cpu = run(src, arch=3)
        assert cpu.state == CpuState.HALTED
        assert list(cpu.mem[256:260]) == [0x55] * 4

    def test_vfill_mnemonic_removed(self) -> None:
        """VFILL is no longer a valid mnemonic — assembler must reject it."""
        from conftest import asm_error as _asm_error

        _asm_error("VFILL.U VC, 0x55\nHLT", arch=3)

    def test_vmov_vv_raw_copy_unchanged(self) -> None:
        """VMOV vv (mode 0) still does raw byte copy."""
        src = (
            "@page 1\nsrc: DB 0x11, 0x22, 0x33, 0x44\n"
            "dst: DB 0, 0, 0, 0\n"
            "@page 0\n"
            "VSET VL, 4\nVSET VA, src\nVSET VC, dst\nVMOV.U VC, VA\nVWAIT\nHLT\n"
        )
        cpu = run(src, arch=3)
        assert cpu.state == CpuState.HALTED
        assert list(cpu.mem[260:264]) == [0x11, 0x22, 0x33, 0x44]

    def test_vmov_vs_gpr_no_longer_accepted(self) -> None:
        """GPR as 3rd operand is no longer parsed as vs (vs is now mem-only)."""
        from conftest import asm_error as _asm_error

        _asm_error("MOV A, 0x77\nVSET VL, 4\nVSET VC, 0x100\nVMOV.U VC, A\nHLT", arch=3)
