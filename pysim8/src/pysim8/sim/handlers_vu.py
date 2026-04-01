"""Vector Unit instruction handlers and async VU executor.

HandlersVuMixin provides:
  - Synchronous handlers (VSET, VFSTAT, VFCLR, VWAIT)
  - Async command issue (VADD..VFILL → push to queue + auto-increment)
  - VU tick (vu_tick: dequeue + execute one command per CPU step)
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from pysim8.isa import (
    VU_ARITH_OPS,
    VU_ASYNC_OPS,
    VU_FMT_ELEM_SIZE,
    VU_INT_FMTS,
    VU_MODE_R,
    VU_MODE_VI,
    VU_MODE_VS,
    VU_MODE_VV,
    VU_UNARY_OPS,
    VU_WINDOW_SIZE,
    Op,
    decode_vfm,
    decode_vu_regs,
)

from .errors import CpuFault, ErrorCode
from .memory import MEMORY_SIZE, PAGE_SIZE
from .registers import exc_to_flags
from .vu import VuCommand, VuQueue, VuRegisters
from .vu_ops import (
    vu_abs,
    vu_arith,
    vu_cmp,
    vu_dot,
    vu_neg,
    vu_read_elem,
    vu_sqrt,
    vu_write_elem,
)

if TYPE_CHECKING:
    from .decoder import DecodedInstr

__all__ = ["HandlersVuMixin"]


class HandlersVuMixin:
    """VU instruction handlers — mixed into CPU."""

    def _build_vu_dispatch(self) -> None:
        d = self._dispatch
        d[Op.VSET_IMM16] = self._h_vset_imm16
        d[Op.VSET_GPR] = self._h_vset_gpr
        d[Op.VSET_MEM] = self._h_vset_mem
        d[Op.VSET_MEMI] = self._h_vset_memi
        d[Op.VFSTAT] = self._h_vfstat
        d[Op.VFCLR] = self._h_vfclr
        d[Op.VWAIT] = self._h_vwait
        # All async ops share one handler
        for op_val in VU_ASYNC_OPS:
            d[Op(op_val)] = self._h_vasync

    def _init_vu(self) -> None:
        """Initialize VU queue. Called from CPU.__init__."""
        self._vu_queue = VuQueue()

    # ── Helpers ───────────────────────────────────────────────────

    def _vu_regs(self) -> VuRegisters:
        vu = self.regs.vu
        if vu is None:
            raise CpuFault(ErrorCode.INVALID_OPCODE, self.regs.ip)
        return vu

    # ── Synchronous handlers ─────────────────────────────────────

    def _h_vset_imm16(self, instr: DecodedInstr) -> None:
        vu = self._vu_regs()
        target = instr.operands[0]
        lo, hi = instr.operands[1], instr.operands[2]
        if target > 4:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        vu.write_reg(target, (hi << 8) | lo)
        self.regs.ip += instr.size

    def _h_vset_gpr(self, instr: DecodedInstr) -> None:
        vu = self._vu_regs()
        target = instr.operands[0]
        packed = instr.operands[1]
        if target > 4:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        rh = (packed >> 2) & 0x03
        rl = packed & 0x03
        val = (self.regs.read(rh) << 8) | self.regs.read(rl)
        vu.write_reg(target, val)
        self.regs.ip += instr.size

    def _h_vset_mem(self, instr: DecodedInstr) -> None:
        vu = self._vu_regs()
        target = instr.operands[0]
        addr = instr.operands[1]
        if target > 4:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        if addr + 1 > 255:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)
        ea = self._direct_addr(addr)
        val = self.mem[ea] | (self.mem[ea + 1] << 8)
        vu.write_reg(target, val)
        self.regs.ip += instr.size

    def _h_vset_memi(self, instr: DecodedInstr) -> None:
        vu = self._vu_regs()
        target = instr.operands[0]
        if target > 4:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        ea = self._indirect_addr(instr.operands[1])
        page_off = ea % PAGE_SIZE
        if page_off + 1 >= PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)
        val = self.mem[ea] | (self.mem[ea + 1] << 8)
        vu.write_reg(target, val)
        self.regs.ip += instr.size

    def _h_vfstat(self, instr: DecodedInstr) -> None:
        vu = self._vu_regs()
        gpr = instr.operands[0]
        if gpr > 3:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        self.regs.write(gpr, vu.vfpsr)
        self.regs.ip += instr.size

    def _h_vfclr(self, instr: DecodedInstr) -> None:
        vu = self._vu_regs()
        vu.vfpsr = 0
        self.regs.ip += instr.size

    def _h_vwait(self, instr: DecodedInstr) -> None:
        """Set VWAIT flag. CPU stalls until VU queue drains via main clock."""
        self._vu_regs()  # validate arch
        # Check for deferred VU fault (OOB detected during earlier tick)
        if self._vu_queue.fault != 0:
            code = self._vu_queue.fault
            self._vu_queue.fault = 0
            raise CpuFault(ErrorCode(code), self.regs.ip)
        if not self._vu_queue.is_empty:
            self._vwait_pending = True
            self._vwait_size = instr.size
        else:
            self.regs.ip += instr.size

    # ── Async command issue ──────────────────────────────────────

    def _h_vasync(self, instr: DecodedInstr) -> None:
        vu = self._vu_regs()
        opcode = int(instr.op)
        fmt, mode, cond = decode_vfm(instr.operands[0])
        dst_code, s1_code, s2_code = decode_vu_regs(instr.operands[1])

        self._validate_vfm(opcode, fmt, mode, cond, instr.operands[1])

        if vu.vl == 0:
            self.regs.ip += instr.size
            return

        cmd = self._vu_build_command(vu, opcode, fmt, mode, cond, dst_code, s1_code, s2_code, instr)
        self._vu_auto_inc(vu, opcode, mode, dst_code, s1_code, s2_code, vu.vl, VU_FMT_ELEM_SIZE.get(fmt, 1))

        while self._vu_queue.is_full:
            self.vu_tick()
        self._vu_queue.enqueue(cmd)
        self.regs.ip += instr.size

    def _vu_build_command(
        self,
        vu: VuRegisters,
        opcode: int,
        fmt: int,
        mode: int,
        cond: int,
        dc: int,
        s1c: int,
        s2c: int,
        instr: DecodedInstr,
    ) -> VuCommand:
        imm = 0
        if mode == VU_MODE_VI:
            for i, b in enumerate(instr.operands[2:]):
                imm |= b << (8 * i)
        elif mode == VU_MODE_VS:
            # GPR broadcast: s2c encodes GPR code, snapshot value
            imm = self.regs.read(s2c)
        return VuCommand(
            op=opcode,
            fmt=fmt,
            mode=mode,
            cond=cond,
            dst_addr=vu.read_ptr(dc),
            s1_addr=vu.read_ptr(s1c),
            s2_addr=vu.read_ptr(s2c) if mode != VU_MODE_VS else 0,
            mask_addr=vu.vm,
            vl=vu.vl,
            imm=imm,
        )

    def _validate_vfm(
        self,
        opcode: int,
        fmt: int,
        mode: int,
        cond: int,
        regs_byte: int,
    ) -> None:
        """Validate VFM byte at decode time. Raises CpuFault on error."""
        if fmt > 6:
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)
        if opcode != Op.VCMP and cond != 0:
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)
        if opcode == Op.VCMP and cond > 5:
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)
        if fmt in VU_INT_FMTS and opcode in (Op.VDOT, Op.VSQRT):
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)
        # GPR broadcast restricted to byte formats (elem_size == 1)
        if mode == VU_MODE_VS and VU_FMT_ELEM_SIZE.get(fmt, 1) > 1:
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)
        # Mode validation per instruction
        if not self._valid_mode(opcode, mode):
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)
        # Reserved bits in regs byte
        if regs_byte & 0x03:
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)

    _VV_ONLY_OPS: frozenset[int] = frozenset({Op.VDOT, Op.VCMP, Op.VSEL})
    _MODE0_ONLY_OPS: frozenset[int] = frozenset({Op.VSQRT, Op.VNEG, Op.VABS, Op.VMOV})

    @staticmethod
    def _valid_mode(opcode: int, mode: int) -> bool:
        if opcode in HandlersVuMixin._VV_ONLY_OPS:
            return mode == 0
        if opcode in HandlersVuMixin._MODE0_ONLY_OPS:
            return mode == 0
        if opcode == Op.VFILL:
            return mode == VU_MODE_VI
        return True  # arithmetic: all modes valid

    _NO_S2_OPS: frozenset[int] = frozenset({Op.VSQRT, Op.VNEG, Op.VABS, Op.VMOV, Op.VFILL})

    @staticmethod
    def _vu_compute_increments(op: int, mode: int, vl: int, sz: int) -> tuple[int, int, int]:
        """Compute (dst_inc, s1_inc, s2_inc) for auto-increment."""
        big_s, small_s = vl * sz, sz
        # dst
        if op == Op.VDOT:
            dst_inc = small_s
        elif op == Op.VCMP:
            dst_inc = vl
        elif mode == VU_MODE_R:
            dst_inc = small_s
        else:
            dst_inc = big_s
        # src1
        s1_inc = 0 if op in (Op.VFILL, Op.VSEL) else big_s
        # src2
        if op in HandlersVuMixin._NO_S2_OPS:
            s2_inc = 0
        elif mode in (VU_MODE_VS, VU_MODE_VI, VU_MODE_R):
            s2_inc = 0
        else:
            s2_inc = big_s
        return dst_inc, s1_inc, s2_inc

    def _vu_auto_inc(
        self,
        vu: VuRegisters,
        op: int,
        mode: int,
        dc: int,
        s1c: int,
        s2c: int,
        vl: int,
        sz: int,
    ) -> None:
        """Apply auto-increment with deduplication."""
        dst_inc, s1_inc, s2_inc = self._vu_compute_increments(op, mode, vl, sz)
        increments: dict[int, int] = {}
        for code, inc in ((dc, dst_inc), (s1c, s1_inc), (s2c, s2_inc)):
            if inc > 0:
                increments[code] = max(increments.get(code, 0), inc)
        for code, inc in increments.items():
            vu.inc_ptr(code, inc)

    # ── VU async execution ───────────────────────────────────────

    def vu_tick(self) -> None:
        """Process one 16-byte window of the front command. Called once per CPU step."""
        if self._vu_queue.is_empty or self._vu_queue.fault != 0:
            return
        cmd = self._vu_queue.peek()
        sz = VU_FMT_ELEM_SIZE.get(cmd.fmt, 1)

        # OOB check on first tick only
        if cmd.progress == 0 and self._vu_check_oob(cmd, sz):
            self._vu_queue.fault = ErrorCode.VU_OOB
            self._vu_queue.flush()
            return

        # Reductions need all elements at once (no partial accumulation)
        is_reduction = cmd.op == Op.VDOT or cmd.mode == VU_MODE_R
        window = cmd.vl if is_reduction else VU_WINDOW_SIZE.get(sz, 4)
        start = cmd.progress
        end = min(start + window, cmd.vl)

        if is_reduction:
            self._vu_exec_reduction_full(cmd, sz)
        else:
            self._vu_exec_window(cmd, sz, start, end)

        cmd.progress = end
        if cmd.progress >= cmd.vl:
            self._vu_queue.dequeue()

    def _vu_exec_window(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        """Execute elements [start, end) of a VU command."""
        op = cmd.op
        if op == Op.VMOV:
            self._vu_win_mov(cmd, sz, start, end)
        elif op == Op.VFILL:
            self._vu_win_fill(cmd, sz, start, end)
        elif op == Op.VCMP:
            self._vu_win_vcmp(cmd, sz, start, end)
        elif op == Op.VSEL:
            self._vu_win_vsel(cmd, sz, start, end)
        elif op in VU_UNARY_OPS:
            self._vu_win_unary(cmd, sz, start, end)
        elif op in VU_ARITH_OPS:
            self._vu_win_arith(cmd, sz, start, end)

    def _vu_rounding_mode(self) -> int:
        return self.regs.fpu.rounding_mode if self.regs.fpu is not None else 0

    def _vu_win_mov(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        for i in range(start, end):
            off = i * sz
            for b in range(sz):
                self.mem[cmd.dst_addr + off + b] = self.mem[cmd.s1_addr + off + b]

    def _vu_win_fill(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        vu = self._vu_regs()
        rm = self._vu_rounding_mode()
        flags = 0
        for i in range(start, end):
            exc = vu_write_elem(self.mem, cmd.dst_addr + i * sz, cmd.fmt, cmd.imm, rm)
            flags |= exc_to_flags(exc)
        vu.vfpsr |= flags

    def _vu_win_vcmp(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        for i in range(start, end):
            a = vu_read_elem(self.mem, cmd.s1_addr + i * sz, cmd.fmt)
            b = vu_read_elem(self.mem, cmd.s2_addr + i * sz, cmd.fmt)
            self.mem[cmd.dst_addr + i] = vu_cmp(a, b, cmd.cond, cmd.fmt)

    def _vu_win_vsel(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        for i in range(start, end):
            if self.mem[cmd.mask_addr + i] == 0:
                off = i * sz
                for b in range(sz):
                    self.mem[cmd.dst_addr + off + b] = self.mem[cmd.s2_addr + off + b]

    def _vu_win_unary(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        vu = self._vu_regs()
        rm = self._vu_rounding_mode()
        op = cmd.op
        flags = 0
        for i in range(start, end):
            val = vu_read_elem(self.mem, cmd.s1_addr + i * sz, cmd.fmt)
            if op == Op.VSQRT:
                result, op_exc = vu_sqrt(val, cmd.fmt, rm)
            elif op == Op.VNEG:
                result, op_exc = vu_neg(val, cmd.fmt)
            else:
                result, op_exc = vu_abs(val, cmd.fmt)
            flags |= exc_to_flags(op_exc)
            exc = vu_write_elem(self.mem, cmd.dst_addr + i * sz, cmd.fmt, result, rm)
            flags |= exc_to_flags(exc)
        vu.vfpsr |= flags

    def _vu_win_arith(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        vu = self._vu_regs()
        rm = self._vu_rounding_mode()
        flags = 0
        for i in range(start, end):
            a = vu_read_elem(self.mem, cmd.s1_addr + i * sz, cmd.fmt)
            b = vu_read_elem(self.mem, cmd.s2_addr + i * sz, cmd.fmt) if cmd.mode == VU_MODE_VV else cmd.imm
            result, op_exc = vu_arith(cmd.op, a, b, cmd.fmt, rm)
            flags |= exc_to_flags(op_exc)
            exc = vu_write_elem(self.mem, cmd.dst_addr + i * sz, cmd.fmt, result, rm)
            flags |= exc_to_flags(exc)
        vu.vfpsr |= flags

    def _vu_exec_reduction_full(self, cmd: VuCommand, sz: int) -> None:
        """Execute VDOT or reduction in one tick (needs all elements)."""
        fmt = cmd.fmt
        rm = self.regs.fpu.rounding_mode if self.regs.fpu is not None else 0
        vu = self._vu_regs()

        if cmd.op == Op.VDOT:
            vals_a = [vu_read_elem(self.mem, cmd.s1_addr + i * sz, fmt) for i in range(cmd.vl)]
            vals_b = [vu_read_elem(self.mem, cmd.s2_addr + i * sz, fmt) for i in range(cmd.vl)]
            result = vu_dot(vals_a, vals_b)
            exc = vu_write_elem(self.mem, cmd.dst_addr, fmt, result, rm)
            vu.vfpsr |= exc_to_flags(exc)
        else:
            acc = vu_read_elem(self.mem, cmd.s1_addr, fmt)
            flags = 0
            for i in range(1, cmd.vl):
                val = vu_read_elem(self.mem, cmd.s1_addr + i * sz, fmt)
                acc, op_exc = vu_arith(cmd.op, acc, val, fmt, rm)
                flags |= exc_to_flags(op_exc)
            exc = vu_write_elem(self.mem, cmd.dst_addr, fmt, acc, rm)
            flags |= exc_to_flags(exc)
            vu.vfpsr |= flags

    def _vu_check_oob(self, cmd: VuCommand, sz: int) -> bool:
        """Check if any operand access is out of bounds."""
        vl = cmd.vl
        # dst footprint depends on operation
        if cmd.op == Op.VCMP:
            dst_bytes = vl  # byte mask
        elif cmd.op == Op.VDOT or cmd.mode == VU_MODE_R:
            dst_bytes = sz  # scalar result
        else:
            dst_bytes = vl * sz
        if cmd.dst_addr + dst_bytes > MEMORY_SIZE:
            return True
        if cmd.s1_addr + vl * sz > MEMORY_SIZE:
            return True
        if cmd.mode == VU_MODE_VV:
            if cmd.s2_addr + vl * sz > MEMORY_SIZE:
                return True
        # Mask pointer for VCMP/VSEL
        if cmd.op in (Op.VCMP, Op.VSEL):
            if cmd.mask_addr + vl > MEMORY_SIZE:
                return True
        return False
