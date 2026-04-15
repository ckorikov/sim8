"""Vector Unit instruction handlers and async VU executor.

HandlersVuMixin provides:
  - Synchronous handlers (VSET, VFSTAT, VFCLR, VWAIT)
  - Async command issue (VADD..VFILL → push to queue + auto-increment)
  - VU tick (vu_tick: dequeue + execute one command per CPU step)
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Callable

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
from .memory import MEM_SIZE, PAGE_SIZE
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
    from pysim8.fp_formats import FpExceptions

    from .decoder import DecodedInstr
    from .handlers import Handler
    from .memory import Memory
    from .registers import RegisterFile

__all__ = ["HandlersVuMixin"]

# Unified (val, fmt, rm) -> (result, exc) callables for each unary VU op.
# vu_sqrt already matches; vu_neg/vu_abs drop the unused rm.
_VU_UNARY_FN: dict[int, Callable[..., tuple[int | float, "FpExceptions"]]] = {
    int(Op.VSQRT): vu_sqrt,
    int(Op.VNEG): lambda val, fmt, rm: vu_neg(val, fmt),
    int(Op.VABS): lambda val, fmt, rm: vu_abs(val, fmt),
}


class HandlersVuMixin:
    """VU instruction handlers — mixed into CPU.

    Expects: self.mem (Memory), self.regs (RegisterFile), self._dispatch,
    self._direct_addr, self._indirect_addr.
    """

    mem: Memory
    regs: RegisterFile
    _dispatch: dict[Op, Handler]

    def _direct_addr(self, offset: int) -> int:
        raise NotImplementedError

    def _indirect_addr(self, encoded: int) -> int:
        raise NotImplementedError

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
        # Op.VFILL (183) is reserved; executing it faults with INVALID_OPCODE
        d[Op.VFILL] = self._h_vfill_reserved

    def _init_vu(self) -> None:
        """Initialize VU queue. Called from CPU.__init__."""
        self._vu_queue = VuQueue()

    # ── Helpers ───────────────────────────────────────────────────

    def _vu_regs(self) -> VuRegisters:
        vu = self.regs.vu
        if vu is None:
            raise CpuFault(ErrorCode.INVALID_OPCODE, self.regs.ip)
        return vu

    def _validate_vu_target(self, target: int) -> None:
        """Raise INVALID_REG if target is not a valid VU register code (0–4)."""
        if target > 4:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)

    def _read_mem16(self, ea: int) -> int:
        """Read a 16-bit little-endian value from memory at ea."""
        return self.mem[ea] | (self.mem[ea + 1] << 8)

    def _decode_vset_gpr_packed(self, packed: int) -> int:
        """Decode VSET_GPR packed byte: single GPR (bit4=1) or high:low pair."""
        if packed & 0x10:
            return self.regs.read(packed & 0x03)
        rh, rl = (packed >> 2) & 0x03, packed & 0x03
        return (self.regs.read(rh) << 8) | self.regs.read(rl)

    # ── Synchronous handlers ─────────────────────────────────────

    def _vu_set_reg(self, instr: DecodedInstr, value: int) -> None:
        """Validate VU target register and write value, then advance IP."""
        target = instr.operands[0]
        self._validate_vu_target(target)
        self._vu_regs().write_reg(target, value)
        self.regs.ip += instr.size

    def _h_vset_imm16(self, instr: DecodedInstr) -> None:
        self._vu_set_reg(instr, (instr.operands[2] << 8) | instr.operands[1])

    def _h_vset_gpr(self, instr: DecodedInstr) -> None:
        self._vu_set_reg(instr, self._decode_vset_gpr_packed(instr.operands[1]))

    def _h_vset_mem(self, instr: DecodedInstr) -> None:
        addr = instr.operands[1]
        if addr + 1 > 255:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)
        self._vu_set_reg(instr, self._read_mem16(self._direct_addr(addr)))

    def _h_vset_memi(self, instr: DecodedInstr) -> None:
        ea = self._indirect_addr(instr.operands[1])
        if ea % PAGE_SIZE + 1 >= PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)
        self._vu_set_reg(instr, self._read_mem16(ea))

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

    def _h_vfill_reserved(self, instr: DecodedInstr) -> None:
        """Op.VFILL (183) is reserved. Always faults with INVALID_OPCODE."""
        raise CpuFault(ErrorCode.INVALID_OPCODE, self.regs.ip)

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
        self._vu_drain_and_enqueue(cmd)
        self.regs.ip += instr.size

    def _vu_build_command(
        self,
        vu: VuRegisters,
        opcode: int,
        fmt: int,
        mode: int,
        cond: int,
        dst_code: int,
        s1_code: int,
        s2_code: int,
        instr: DecodedInstr,
    ) -> VuCommand:
        imm = 0
        if mode == VU_MODE_VI:
            for i, b in enumerate(instr.operands[2:]):
                imm |= b << (8 * i)
        elif mode == VU_MODE_VS:
            # GPR broadcast: s2_code encodes GPR code, snapshot value
            imm = self.regs.read(s2_code)
        return VuCommand(
            op=opcode,
            fmt=fmt,
            mode=mode,
            cond=cond,
            dst_addr=vu.read_ptr(dst_code),
            s1_addr=vu.read_ptr(s1_code),
            s2_addr=vu.read_ptr(s2_code) if mode != VU_MODE_VS else 0,
            mask_addr=vu.vm,
            vl=vu.vl,
            imm=imm,
        )

    def _vu_drain_and_enqueue(self, cmd: VuCommand) -> None:
        """Drain the VU queue until space is available, then enqueue cmd."""
        while self._vu_queue.is_full:
            self.vu_tick()
        self._vu_queue.enqueue(cmd)

    def _validate_vfm(
        self,
        opcode: int,
        fmt: int,
        mode: int,
        cond: int,
        regs_byte: int,
    ) -> None:
        """Validate VFM byte at decode time. Raises CpuFault on error."""

        def fault() -> None:
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)

        if fmt > 6:
            fault()
        if opcode != Op.VCMP and cond != 0:
            fault()
        if opcode == Op.VCMP and cond > 5:
            fault()
        if fmt in VU_INT_FMTS and opcode in (Op.VDOT, Op.VSQRT):
            fault()
        # GPR broadcast restricted to byte formats (elem_size == 1)
        if mode == VU_MODE_VS and VU_FMT_ELEM_SIZE.get(fmt, 1) > 1:
            fault()
        # Mode validation per instruction
        if not self._valid_mode(opcode, mode):
            fault()
        # Reserved bits in regs byte
        if regs_byte & 0x03:
            fault()

    _VV_ONLY_OPS: frozenset[int] = frozenset({Op.VDOT, Op.VCMP, Op.VSEL})
    _MODE0_ONLY_OPS: frozenset[int] = frozenset({Op.VSQRT, Op.VNEG, Op.VABS, Op.VGATHER, Op.VSCATTER})

    @staticmethod
    def _valid_mode(opcode: int, mode: int) -> bool:
        if opcode in HandlersVuMixin._VV_ONLY_OPS:
            return mode == 0
        if opcode in HandlersVuMixin._MODE0_ONLY_OPS:
            return mode == 0
        if opcode == Op.VMOV:
            return mode in (0, VU_MODE_VI)
        if opcode == Op.VFILL:
            return mode == VU_MODE_VI
        return True  # arithmetic: all modes valid

    _NO_S2_OPS: frozenset[int] = frozenset({Op.VSQRT, Op.VNEG, Op.VABS, Op.VMOV, Op.VFILL, Op.VGATHER, Op.VSCATTER})

    @staticmethod
    def _vu_dst_inc(op: int, mode: int, vl: int, sz: int) -> int:
        """Destination auto-increment: reduction/dot writes one element, others write the full vector."""
        if op == Op.VDOT:
            return sz
        if op == Op.VCMP:
            return vl
        if op == Op.VGATHER:
            return 0  # data-dependent, user must VSET
        if mode == VU_MODE_R:
            return sz
        return vl * sz

    @staticmethod
    def _vu_s1_inc(op: int, vl: int, sz: int) -> int:
        """Source-1 auto-increment: zero for VFILL/VSEL (no src1 consumed), else full vector."""
        if op in (Op.VFILL, Op.VSEL, Op.VSCATTER):
            return 0  # VSCATTER: data-dependent, user must VSET
        return vl * sz

    @staticmethod
    def _vu_s2_inc(op: int, mode: int, vl: int, sz: int) -> int:
        """Source-2 auto-increment: zero for unary ops, scalar/imm modes, or reduce; else full vector."""
        if op in HandlersVuMixin._NO_S2_OPS:
            return 0
        if mode in (VU_MODE_VS, VU_MODE_VI, VU_MODE_R):
            return 0
        return vl * sz

    @staticmethod
    def _vu_compute_increments(op: int, mode: int, vl: int, sz: int) -> tuple[int, int, int]:
        """Compute (dst_inc, s1_inc, s2_inc) for auto-increment."""
        return (
            HandlersVuMixin._vu_dst_inc(op, mode, vl, sz),
            HandlersVuMixin._vu_s1_inc(op, vl, sz),
            HandlersVuMixin._vu_s2_inc(op, mode, vl, sz),
        )

    def _vu_auto_inc(
        self,
        vu: VuRegisters,
        op: int,
        mode: int,
        dst_code: int,
        s1_code: int,
        s2_code: int,
        vl: int,
        sz: int,
    ) -> None:
        """Apply auto-increment with deduplication."""
        dst_inc, s1_inc, s2_inc = self._vu_compute_increments(op, mode, vl, sz)
        increments: dict[int, int] = {}
        for code, inc in ((dst_code, dst_inc), (s1_code, s1_inc), (s2_code, s2_inc)):
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
        elif op == Op.VGATHER:
            self._vu_win_gather(cmd, sz, start, end)
        elif op == Op.VSCATTER:
            self._vu_win_scatter(cmd, sz, start, end)
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

    def _vu_accumulate_flags(self, start: int, end: int, elem_fn: Callable[[int], int]) -> None:
        """Apply elem_fn for each element index and accumulate VFPSR exception flags."""
        flags = 0
        for i in range(start, end):
            flags |= elem_fn(i)
        self._vu_regs().vfpsr |= flags

    def _vu_win_fill(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        rm = self._vu_rounding_mode()
        self._vu_accumulate_flags(
            start,
            end,
            lambda i: exc_to_flags(vu_write_elem(self.mem, cmd.dst_addr + i * sz, cmd.fmt, cmd.imm, rm)),
        )

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

    def _vu_win_gather(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        """Mask compress: copy src elements where mask is nonzero into packed dst."""
        for i in range(start, end):
            if self.mem[cmd.mask_addr + i] == 0:
                continue
            dst_off = cmd.dst_addr + cmd.compact_idx * sz
            if dst_off + sz > MEM_SIZE:
                self._vu_queue.fault = ErrorCode.VU_OOB
                self._vu_queue.flush()
                return
            for b in range(sz):
                self.mem[dst_off + b] = self.mem[cmd.s1_addr + i * sz + b]
            cmd.compact_idx += 1

    def _vu_win_scatter(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        """Mask expand: scatter packed src elements into dst where mask is nonzero."""
        for i in range(start, end):
            if self.mem[cmd.mask_addr + i] == 0:
                continue
            src_off = cmd.s1_addr + cmd.compact_idx * sz
            if src_off + sz > MEM_SIZE:
                self._vu_queue.fault = ErrorCode.VU_OOB
                self._vu_queue.flush()
                return
            for b in range(sz):
                self.mem[cmd.dst_addr + i * sz + b] = self.mem[src_off + b]
            cmd.compact_idx += 1

    def _vu_win_unary(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        rm = self._vu_rounding_mode()
        unary_fn = _VU_UNARY_FN[cmd.op]

        def _elem(i: int) -> int:
            val = vu_read_elem(self.mem, cmd.s1_addr + i * sz, cmd.fmt)
            result, op_exc = unary_fn(val, cmd.fmt, rm)
            return exc_to_flags(op_exc) | exc_to_flags(
                vu_write_elem(self.mem, cmd.dst_addr + i * sz, cmd.fmt, result, rm)
            )

        self._vu_accumulate_flags(start, end, _elem)

    def _vu_win_arith(self, cmd: VuCommand, sz: int, start: int, end: int) -> None:
        rm = self._vu_rounding_mode()
        is_vv = cmd.mode == VU_MODE_VV

        def _elem(i: int) -> int:
            a = vu_read_elem(self.mem, cmd.s1_addr + i * sz, cmd.fmt)
            b = vu_read_elem(self.mem, cmd.s2_addr + i * sz, cmd.fmt) if is_vv else cmd.imm
            result, op_exc = vu_arith(cmd.op, a, b, cmd.fmt, rm)
            return exc_to_flags(op_exc) | exc_to_flags(
                vu_write_elem(self.mem, cmd.dst_addr + i * sz, cmd.fmt, result, rm)
            )

        self._vu_accumulate_flags(start, end, _elem)

    def _vu_exec_reduction_full(self, cmd: VuCommand, sz: int) -> None:
        """Execute VDOT or reduction in one tick (needs all elements)."""
        if cmd.op == Op.VDOT:
            self._vu_exec_vdot(cmd, sz)
        else:
            self._vu_exec_reduce(cmd, sz)

    def _vu_exec_vdot(self, cmd: VuCommand, sz: int) -> None:
        """Read two vectors, compute dot product, write scalar to dst."""
        fmt, rm, vu = cmd.fmt, self._vu_rounding_mode(), self._vu_regs()
        vals_a = [vu_read_elem(self.mem, cmd.s1_addr + i * sz, fmt) for i in range(cmd.vl)]
        vals_b = [vu_read_elem(self.mem, cmd.s2_addr + i * sz, fmt) for i in range(cmd.vl)]
        exc = vu_write_elem(self.mem, cmd.dst_addr, fmt, vu_dot(vals_a, vals_b), rm)
        vu.vfpsr |= exc_to_flags(exc)

    def _vu_exec_reduce(self, cmd: VuCommand, sz: int) -> None:
        """Accumulate s1 elements left-to-right with op, write scalar to dst."""
        fmt, rm, vu = cmd.fmt, self._vu_rounding_mode(), self._vu_regs()
        acc = vu_read_elem(self.mem, cmd.s1_addr, fmt)
        flags = 0
        for i in range(1, cmd.vl):
            val = vu_read_elem(self.mem, cmd.s1_addr + i * sz, fmt)
            acc, op_exc = vu_arith(cmd.op, acc, val, fmt, rm)
            flags |= exc_to_flags(op_exc)
        exc = vu_write_elem(self.mem, cmd.dst_addr, fmt, acc, rm)
        vu.vfpsr |= flags | exc_to_flags(exc)

    @staticmethod
    def _vu_dst_footprint(cmd: VuCommand, sz: int) -> int:
        """Return dst byte footprint: byte mask (VCMP), scalar (VDOT/reduce), or full vector."""
        if cmd.op == Op.VCMP:
            return cmd.vl
        if cmd.op == Op.VDOT or cmd.mode == VU_MODE_R:
            return sz
        return cmd.vl * sz

    _GATHER_OPS: frozenset[int] = frozenset({Op.VGATHER, Op.VSCATTER})

    def _vu_check_oob(self, cmd: VuCommand, sz: int) -> bool:
        """Check if any operand access is out of bounds."""
        vl = cmd.vl
        dst_bytes = self._vu_dst_footprint(cmd, sz)
        if cmd.dst_addr + dst_bytes > MEM_SIZE:
            return True
        # s1 footprint: VFILL/VSEL don't read s1; VSCATTER reads data-dependent count
        if cmd.op not in (Op.VFILL, Op.VSEL, Op.VSCATTER):
            if cmd.s1_addr + vl * sz > MEM_SIZE:
                return True
        # s2 footprint for VV mode (not for VGATHER/VSCATTER which are unary)
        if cmd.mode == VU_MODE_VV and cmd.op not in self._GATHER_OPS:
            if cmd.s2_addr + vl * sz > MEM_SIZE:
                return True
        # Mask pointer for VCMP/VSEL/VGATHER/VSCATTER
        if cmd.op in (Op.VCMP, Op.VSEL) or cmd.op in self._GATHER_OPS:
            if cmd.mask_addr + vl > MEM_SIZE:
                return True
        return False
