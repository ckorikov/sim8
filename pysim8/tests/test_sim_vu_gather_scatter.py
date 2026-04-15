"""VGATHER (184) and VSCATTER (185) integration tests.

VGATHER: mask compress -- pick elements where mask[i]!=0, pack contiguous.
    j=0; for i in 0..VL-1: if mem[VM+i]: dst[j++] = src[i]
    Auto-increment: src(VA) += VL*sz, dst(VB) no advance, VM no advance.

VSCATTER: mask expand -- unpack contiguous into positions where mask[i]!=0.
    j=0; for i in 0..VL-1: if mem[VM+i]: dst[i] = src[j++]
    Auto-increment: dst(VB) += VL*sz, src(VA) no advance, VM no advance.

Both are unary (vv mode only), support all formats, raw byte copy,
no FP exceptions.
"""

from __future__ import annotations

import pytest

from pysim8.isa import (
    Op,
    VU_FMT_ELEM_SIZE,
    VU_FMT_U,
    VU_MODE_VV,
    encode_vfm,
    encode_vu_regs,
)
from pysim8.sim.cpu import CPU
from pysim8.sim.registers import CpuState

from conftest import run


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


def vasync(op: int, fmt: int, mode: int, dst: int, s1: int, s2: int) -> list[int]:
    """Encode async VU instruction (3 bytes: opcode, VFM, regs)."""
    return [op, encode_vfm(fmt, mode), encode_vu_regs(dst, s1, s2)]


# Register codes: VA=0, VB=1, VC=2, VM=3, VL=4
VA, VB, VC, VM, VL_REG = 0, 1, 2, 3, 4

# Memory layout constants
SRC_ADDR = 0x0100
DST_ADDR = 0x0200
MASK_ADDR = 0x0300


def _setup_gather_test(
    cpu: CPU,
    src: list[int],
    mask: list[int],
    vl: int,
    *,
    src_addr: int = SRC_ADDR,
    dst_addr: int = DST_ADDR,
    mask_addr: int = MASK_ADDR,
) -> list[int]:
    """Place src and mask in memory, return bytecode to set VU regs.

    VGATHER reads from s1 (VA=src) into dst (VB=dst), mask from VM.
    """
    for i, v in enumerate(src):
        cpu.mem[src_addr + i] = v
    for i, v in enumerate(mask):
        cpu.mem[mask_addr + i] = v
    return vset_imm16(VA, src_addr) + vset_imm16(VB, dst_addr) + vset_imm16(VM, mask_addr) + vset_imm16(VL_REG, vl)


def _setup_scatter_test(
    cpu: CPU,
    src: list[int],
    mask: list[int],
    vl: int,
    *,
    src_addr: int = SRC_ADDR,
    dst_addr: int = DST_ADDR,
    mask_addr: int = MASK_ADDR,
) -> list[int]:
    """Place src and mask in memory, return bytecode to set VU regs.

    VSCATTER reads from s1 (VA=src packed) into dst (VB=expanded), mask from VM.
    """
    for i, v in enumerate(src):
        cpu.mem[src_addr + i] = v
    for i, v in enumerate(mask):
        cpu.mem[mask_addr + i] = v
    return vset_imm16(VA, src_addr) + vset_imm16(VB, dst_addr) + vset_imm16(VM, mask_addr) + vset_imm16(VL_REG, vl)


# ── VGATHER tests ───────────────────────────────────────────────


class TestVGather:
    def test_stride4_mask(self) -> None:
        """Every 4th element selected -- stride-4 mask pattern."""
        cpu = cpu3()
        vl = 8
        src = list(range(10, 10 + vl))  # [10..17]
        mask = [1, 0, 0, 0, 1, 0, 0, 0]  # pick index 0, 4
        setup = _setup_gather_test(cpu, src, mask, vl)
        code = (
            setup + vasync(int(Op.VGATHER), VU_FMT_U, VU_MODE_VV, VB, VA, 0) + [169, 0]  # VWAIT; HLT
        )
        cpu.load(code)
        # Re-write src/mask after load (load resets memory)
        for i, v in enumerate(src):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        cpu.run()
        assert cpu.mem[DST_ADDR] == 10  # src[0]
        assert cpu.mem[DST_ADDR + 1] == 14  # src[4]

    def test_all_ones_mask(self) -> None:
        """All-ones mask copies everything contiguously."""
        cpu = cpu3()
        vl = 4
        src = [0xAA, 0xBB, 0xCC, 0xDD]
        mask = [1, 1, 1, 1]
        setup = _setup_gather_test(cpu, src, mask, vl)
        code = setup + vasync(int(Op.VGATHER), VU_FMT_U, VU_MODE_VV, VB, VA, 0) + [169, 0]
        cpu.load(code)
        for i, v in enumerate(src):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        cpu.run()
        result = [cpu.mem[DST_ADDR + i] for i in range(4)]
        assert result == [0xAA, 0xBB, 0xCC, 0xDD]

    def test_all_zeros_mask(self) -> None:
        """All-zeros mask writes nothing; dst memory unchanged."""
        cpu = cpu3()
        vl = 4
        src = [0xAA, 0xBB, 0xCC, 0xDD]
        mask = [0, 0, 0, 0]
        sentinel = 0x42
        setup = _setup_gather_test(cpu, src, mask, vl)
        code = setup + vasync(int(Op.VGATHER), VU_FMT_U, VU_MODE_VV, VB, VA, 0) + [169, 0]
        cpu.load(code)
        for i, v in enumerate(src):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        # Fill dst with sentinel to verify nothing is overwritten
        for i in range(vl):
            cpu.mem[DST_ADDR + i] = sentinel
        cpu.run()
        for i in range(vl):
            assert cpu.mem[DST_ADDR + i] == sentinel

    def test_multi_window(self) -> None:
        """VL=16 with U format: window=8, so 2 windows. compact_idx persists."""
        cpu = cpu3()
        vl = 16
        src = list(range(vl))  # [0..15]
        # Alternating mask: pick even indices
        mask = [1, 0] * 8
        setup = _setup_gather_test(cpu, src, mask, vl)
        code = setup + vasync(int(Op.VGATHER), VU_FMT_U, VU_MODE_VV, VB, VA, 0) + [169, 0]
        cpu.load(code)
        for i, v in enumerate(src):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        cpu.run()
        # Even indices: 0, 2, 4, 6, 8, 10, 12, 14
        expected = [0, 2, 4, 6, 8, 10, 12, 14]
        result = [cpu.mem[DST_ADDR + i] for i in range(len(expected))]
        assert result == expected

    def test_auto_increment(self) -> None:
        """VGATHER: VA (src) += VL*sz, VB (dst) unchanged, VM unchanged."""
        cpu = cpu3()
        vl = 4
        src = [1, 2, 3, 4]
        mask = [1, 1, 1, 1]
        setup = _setup_gather_test(cpu, src, mask, vl)
        code = setup + vasync(int(Op.VGATHER), VU_FMT_U, VU_MODE_VV, VB, VA, 0) + [169, 0]
        cpu.load(code)
        for i, v in enumerate(src):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        cpu.run()
        vu = cpu.regs.vu
        # src (VA) advances by VL * elem_size(U=1) = 4
        assert vu.va == SRC_ADDR + vl * VU_FMT_ELEM_SIZE[VU_FMT_U]
        # dst (VB) does not advance
        assert vu.vb == DST_ADDR
        # mask (VM) does not advance
        assert vu.vm == MASK_ADDR


# ── VSCATTER tests ──────────────────────────────────────────────


class TestVScatter:
    def test_stride4_mask_expand(self) -> None:
        """Expand packed elements into positions where mask[i]!=0."""
        cpu = cpu3()
        vl = 8
        # Packed source: only 2 elements will be consumed
        packed_src = [0xAA, 0xBB, 0, 0, 0, 0, 0, 0]
        mask = [1, 0, 0, 0, 1, 0, 0, 0]
        setup = _setup_scatter_test(cpu, packed_src, mask, vl)
        code = setup + vasync(int(Op.VSCATTER), VU_FMT_U, VU_MODE_VV, VB, VA, 0) + [169, 0]
        cpu.load(code)
        for i, v in enumerate(packed_src):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        cpu.run()
        # Position 0: mask=1 -> src[j=0]=0xAA
        assert cpu.mem[DST_ADDR + 0] == 0xAA
        # Position 4: mask=1 -> src[j=1]=0xBB
        assert cpu.mem[DST_ADDR + 4] == 0xBB
        # Positions with mask=0 should be unchanged (0 from load)
        for i in [1, 2, 3, 5, 6, 7]:
            assert cpu.mem[DST_ADDR + i] == 0

    def test_round_trip(self) -> None:
        """VGATHER then VSCATTER with the same mask recovers original layout."""
        cpu = cpu3()
        vl = 8
        original = [10, 20, 30, 40, 50, 60, 70, 80]
        mask = [1, 0, 1, 0, 1, 0, 1, 0]  # pick even indices
        gather_dst = 0x0400  # intermediate packed buffer
        scatter_dst = 0x0500  # final expanded buffer

        # Set up source and mask
        for i, v in enumerate(original):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v

        # Phase 1: VGATHER from SRC into gather_dst
        # Phase 2: VSCATTER from gather_dst into scatter_dst
        code = (
            # VGATHER: VA=src, VB=gather_dst, VM=mask
            vset_imm16(VA, SRC_ADDR)
            + vset_imm16(VB, gather_dst)
            + vset_imm16(VM, MASK_ADDR)
            + vset_imm16(VL_REG, vl)
            + vasync(int(Op.VGATHER), VU_FMT_U, VU_MODE_VV, VB, VA, 0)
            + [169]  # VWAIT
            # VSCATTER: VA=gather_dst (packed src), VB=scatter_dst, VM=mask
            # Reset VA to gather_dst (no auto-inc on VB for gather)
            + vset_imm16(VA, gather_dst)
            + vset_imm16(VB, scatter_dst)
            + vset_imm16(VM, MASK_ADDR)
            + vset_imm16(VL_REG, vl)
            + vasync(int(Op.VSCATTER), VU_FMT_U, VU_MODE_VV, VB, VA, 0)
            + [169, 0]  # VWAIT; HLT
        )
        cpu.load(code)
        # Re-write data after load
        for i, v in enumerate(original):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        cpu.run()

        # Positions where mask=1 should have original values
        assert cpu.mem[scatter_dst + 0] == 10
        assert cpu.mem[scatter_dst + 2] == 30
        assert cpu.mem[scatter_dst + 4] == 50
        assert cpu.mem[scatter_dst + 6] == 70
        # Positions where mask=0 should be 0 (untouched)
        assert cpu.mem[scatter_dst + 1] == 0
        assert cpu.mem[scatter_dst + 3] == 0
        assert cpu.mem[scatter_dst + 5] == 0
        assert cpu.mem[scatter_dst + 7] == 0

    def test_auto_increment(self) -> None:
        """VSCATTER: VB (dst) += VL*sz, VA (src) unchanged, VM unchanged."""
        cpu = cpu3()
        vl = 4
        packed_src = [0xAA, 0xBB, 0xCC, 0xDD]
        mask = [1, 1, 1, 1]
        setup = _setup_scatter_test(cpu, packed_src, mask, vl)
        code = setup + vasync(int(Op.VSCATTER), VU_FMT_U, VU_MODE_VV, VB, VA, 0) + [169, 0]
        cpu.load(code)
        for i, v in enumerate(packed_src):
            cpu.mem[SRC_ADDR + i] = v
        for i, v in enumerate(mask):
            cpu.mem[MASK_ADDR + i] = v
        cpu.run()
        vu = cpu.regs.vu
        # dst (VB) advances by VL * elem_size(U=1) = 4
        assert vu.vb == DST_ADDR + vl * VU_FMT_ELEM_SIZE[VU_FMT_U]
        # src (VA) does not advance
        assert vu.va == SRC_ADDR
        # mask (VM) does not advance
        assert vu.vm == MASK_ADDR


# ── VL=0 no-op ──────────────────────────────────────────────────


class TestVGatherScatterVLZero:
    @pytest.mark.parametrize(
        "op",
        [
            pytest.param(Op.VGATHER, id="vgather"),
            pytest.param(Op.VSCATTER, id="vscatter"),
        ],
    )
    def test_vl_zero_noop(self, op: Op) -> None:
        """VL=0 means no work; pointers unchanged, no memory writes."""
        cpu = cpu3()
        sentinel = 0x42
        code = (
            vset_imm16(VA, SRC_ADDR)
            + vset_imm16(VB, DST_ADDR)
            + vset_imm16(VM, MASK_ADDR)
            + vset_imm16(VL_REG, 0)
            + vasync(int(op), VU_FMT_U, VU_MODE_VV, VB, VA, 0)
            + [169, 0]
        )
        cpu.load(code)
        # Fill dst with sentinel
        for i in range(8):
            cpu.mem[DST_ADDR + i] = sentinel
        cpu.run()
        vu = cpu.regs.vu
        assert vu.va == SRC_ADDR
        assert vu.vb == DST_ADDR
        assert vu.vm == MASK_ADDR
        # Dst memory untouched
        for i in range(8):
            assert cpu.mem[DST_ADDR + i] == sentinel
