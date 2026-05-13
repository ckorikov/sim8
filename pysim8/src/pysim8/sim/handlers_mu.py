"""Matrix Unit instruction handlers and async MU executor.

HandlersMuMixin provides:
  - Synchronous handlers (MSET, MFSTAT, MFCLR, MWAIT)
  - Async command issue (MMUL → push to queue + auto-increment)
  - MU tick (mu_tick: dequeue + execute one command per CPU step)
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from pysim8.fp_arithmetic import fp_add, fp_mul
from pysim8.isa import (
    MU_ASYNC_OPS,
    MU_FMT_ELEM_SIZE,
    MU_FP_FMTS,
    MU_INT_FMTS,
    VU_FMT_F,
    Op,
    decode_mfm,
    decode_vu_regs,
)

from .errors import CpuFault, ErrorCode
from .memory import MEM_SIZE
from .mu import MuCommand, MuQueue, MuRegisters
from .registers import exc_to_flags
from .vu_ops import vu_read_elem, vu_write_elem

if TYPE_CHECKING:
    from .decoder import DecodedInstr
    from .handlers import Handler
    from .memory import Memory
    from .registers import RegisterFile

__all__ = ["HandlersMuMixin"]


class HandlersMuMixin:
    """MU instruction handlers — mixed into CPU."""

    mem: Memory
    regs: RegisterFile
    _dispatch: dict[Op, Handler]

    def _build_mu_dispatch(self) -> None:
        d = self._dispatch
        d[Op.MSET_IMM16] = self._h_mset_imm16
        d[Op.MSET_GPR] = self._h_mset_gpr
        d[Op.MFSTAT] = self._h_mfstat
        d[Op.MFCLR] = self._h_mfclr
        d[Op.MWAIT] = self._h_mwait
        for op_val in MU_ASYNC_OPS:
            d[Op(op_val)] = self._h_masync

    def _init_mu(self) -> None:
        """Initialize MU queue + registers. Called from CPU.__init__."""
        self._mu_queue = MuQueue()
        self._mu_regs = MuRegisters()
        self._mwait_pending = False
        self._mwait_size = 0

    # ── Helpers ───────────────────────────────────────────────────

    def _validate_mu_target(self, target: int) -> None:
        """Raise INVALID_REG if target is not a valid MU register code (0–5)."""
        if target > 5:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)

    # ── Synchronous handlers ─────────────────────────────────────

    def _mu_set_reg(self, instr: DecodedInstr, value: int) -> None:
        target = instr.operands[0]
        self._validate_mu_target(target)
        self._mu_regs.write_reg(target, value)
        self.regs.ip += instr.size

    def _h_mset_imm16(self, instr: DecodedInstr) -> None:
        # operands: [target, lo, hi]
        self._mu_set_reg(instr, (instr.operands[2] << 8) | instr.operands[1])

    def _h_mset_gpr(self, instr: DecodedInstr) -> None:
        # operands: [target, packed]; packed bit 4 = single-GPR flag
        packed = instr.operands[1]
        if packed & 0x10:
            value = self.regs.read(packed & 0x03)
        else:
            rh, rl = (packed >> 2) & 0x03, packed & 0x03
            value = (self.regs.read(rh) << 8) | self.regs.read(rl)
        self._mu_set_reg(instr, value)

    def _h_mfstat(self, instr: DecodedInstr) -> None:
        gpr = instr.operands[0]
        if gpr > 3:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        self.regs.write(gpr, self._mu_regs.mfpsr)
        self.regs.ip += instr.size

    def _h_mfclr(self, instr: DecodedInstr) -> None:
        self._mu_regs.mfpsr = 0
        self.regs.ip += instr.size

    def _h_mwait(self, instr: DecodedInstr) -> None:
        """Set MWAIT flag. CPU stalls until MU queue drains via main clock."""
        if self._mu_queue.fault != 0:
            code = self._mu_queue.fault
            self._mu_queue.fault = 0
            raise CpuFault(ErrorCode(code), self.regs.ip)
        if not self._mu_queue.is_empty:
            self._mwait_pending = True
            self._mwait_size = instr.size
        else:
            self.regs.ip += instr.size

    # ── Async command issue ──────────────────────────────────────

    def _h_masync(self, instr: DecodedInstr) -> None:
        opcode = int(instr.op)
        mfm = instr.operands[0]
        regs_byte = instr.operands[1]
        fmt, a_col, b_col, c_col = decode_mfm(mfm)
        dst, src1, src2 = decode_vu_regs(regs_byte)

        self._validate_mfm(opcode, mfm, regs_byte, fmt)

        mu = self._mu_regs
        m, n, k = mu.mm, mu.mn, mu.mk

        if m == 0 or n == 0 or k == 0:
            self.regs.ip += instr.size
            return

        sz = MU_FMT_ELEM_SIZE.get(fmt, 1)
        accumulate = opcode == int(Op.MMAD)
        cmd = MuCommand(
            op=opcode,
            fmt=fmt,
            a_col=a_col,
            b_col=b_col,
            c_col=c_col,
            accumulate=accumulate,
            a_addr=mu.read_ptr(src1),
            b_addr=mu.read_ptr(src2),
            c_addr=mu.read_ptr(dst),
            m=m,
            n=n,
            k=k,
        )
        # Auto-increment MA / MB only; MC stays put so K-loop accumulation
        # does not need a re-MSET. Deduplicate when same code appears as both
        # A and B operand (advance once by the largest stride).
        increments: dict[int, int] = {}
        for code, inc in (
            (src1, m * k * sz),
            (src2, k * n * sz),
        ):
            if inc > 0:
                increments[code] = max(increments.get(code, 0), inc)
        for code, inc in increments.items():
            mu.inc_ptr(code, inc)

        while self._mu_queue.is_full:
            self.mu_tick()
        self._mu_queue.enqueue(cmd)
        self.regs.ip += instr.size

    def _validate_mfm(self, opcode: int, mfm: int, regs_byte: int, fmt: int) -> None:
        """Decode-time validation for MMUL/MMAD."""

        def fault() -> None:
            raise CpuFault(ErrorCode.VU_FORMAT, self.regs.ip)

        if mfm & 0xC0:
            fault()
        if fmt not in MU_FP_FMTS and fmt not in MU_INT_FMTS:
            fault()
        if regs_byte & 0x03:
            fault()
        dst, src1, src2 = decode_vu_regs(regs_byte)
        if dst > 2 or src1 > 2 or src2 > 2:
            fault()

    # ── MU async execution ───────────────────────────────────────

    def mu_tick(self) -> None:
        """Execute the front MMUL command in one tick (whole matrix at a time).

        For simplicity MU is fully blocking per command (unlike VU's window
        model). Each tick processes one queued MMUL end-to-end.
        """
        if self._mu_queue.is_empty or self._mu_queue.fault != 0:
            return
        cmd = self._mu_queue.peek()
        sz = MU_FMT_ELEM_SIZE.get(cmd.fmt, 1)

        # OOB validation
        if self._mu_validate_oob(cmd, sz):
            self._mu_queue.fault = ErrorCode.VU_OOB
            self._mu_queue.flush()
            return

        self._mu_exec_mmul(cmd, sz)
        self._mu_queue.dequeue()

    @staticmethod
    def _mu_validate_oob(cmd: MuCommand, sz: int) -> bool:
        """Check A, B, C extents against MEM_SIZE."""
        m, n, k = cmd.m, cmd.n, cmd.k
        if cmd.a_addr + m * k * sz > MEM_SIZE:
            return True
        if cmd.b_addr + k * n * sz > MEM_SIZE:
            return True
        if cmd.c_addr + m * n * 4 > MEM_SIZE:
            return True
        return False

    def _mu_exec_mmul(self, cmd: MuCommand, sz: int) -> None:
        """Execute C = A @ B (MMUL) or C += A @ B (MMAD), all layout modes."""
        rm = self._mu_rounding_mode()
        m, n, k = cmd.m, cmd.n, cmd.k
        fmt = cmd.fmt
        is_int = fmt in MU_INT_FMTS

        flags = 0
        for i in range(m):
            for j in range(n):
                if is_int:
                    acc_int = 0
                    for kk in range(k):
                        a_off = ((kk * m + i) if cmd.a_col else (i * k + kk)) * sz
                        b_off = ((j * k + kk) if cmd.b_col else (kk * n + j)) * sz
                        a = vu_read_elem(self.mem, cmd.a_addr + a_off, fmt)
                        b = vu_read_elem(self.mem, cmd.b_addr + b_off, fmt)
                        acc_int = (acc_int + int(a) * int(b)) & 0xFFFFFFFF
                    c_off = ((j * m + i) if cmd.c_col else (i * n + j)) * 4
                    if cmd.accumulate:
                        c_old_raw = int.from_bytes(
                            bytes(self.mem[cmd.c_addr + c_off + b] for b in range(4)),
                            "little",
                        )
                        acc_int = (acc_int + c_old_raw) & 0xFFFFFFFF
                    raw = acc_int.to_bytes(4, "little")
                    for b, byte in enumerate(raw):
                        self.mem[cmd.c_addr + c_off + b] = byte
                else:
                    acc = 0.0
                    for kk in range(k):
                        a_off = ((kk * m + i) if cmd.a_col else (i * k + kk)) * sz
                        b_off = ((j * k + kk) if cmd.b_col else (kk * n + j)) * sz
                        a = vu_read_elem(self.mem, cmd.a_addr + a_off, fmt)
                        b = vu_read_elem(self.mem, cmd.b_addr + b_off, fmt)
                        prod, exc = fp_mul(float(a), float(b), fmt, rm)
                        flags |= exc_to_flags(exc)
                        sum_, exc = fp_add(acc, prod, fmt, rm)
                        flags |= exc_to_flags(exc)
                        acc = sum_
                    c_off = ((j * m + i) if cmd.c_col else (i * n + j)) * 4
                    if cmd.accumulate:
                        c_old = vu_read_elem(self.mem, cmd.c_addr + c_off, VU_FMT_F)
                        acc, exc = fp_add(float(c_old), acc, VU_FMT_F, rm)
                        flags |= exc_to_flags(exc)
                    exc = vu_write_elem(self.mem, cmd.c_addr + c_off, VU_FMT_F, acc, rm)
                    flags |= exc_to_flags(exc)

        if not is_int:
            self._mu_regs.mfpsr |= flags

    def _mu_rounding_mode(self) -> int:
        return self.regs.fpu.rounding_mode if self.regs.fpu is not None else 0
