"""Instruction handlers: dispatch table, address resolution, factories."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

from pysim8.isa import Op, Reg, decode_regaddr, BY_CODE_FP

from .alu import ALU
from .decoder import DecodedInsn
from .errors import CpuFault, ErrorCode
from .memory import Memory

if TYPE_CHECKING:
    from .registers import RegisterFile

_SP = Reg.SP
_DP = Reg.DP

__all__ = ["HandlersMixin", "Handler"]

type Handler = Callable[[DecodedInsn], None]


class HandlersMixin:
    """Mixin providing instruction handlers for CPU.

    Expects: self.mem (Memory), self.regs (RegisterFile),
    self._dispatch (dict[Op, Handler]).
    """

    mem: Memory
    regs: RegisterFile
    _dispatch: dict[Op, Handler]

    # ── Address resolution ─────────────────────────────────────────────

    def _direct_addr(self, offset: int) -> int:
        """Compute absolute address: DP * PAGE_SIZE + offset."""
        return self.regs.dp * Memory.PAGE_SIZE + offset

    def _indirect_addr(self, encoded: int) -> int:
        """Decode register indirect address from encoded byte."""
        reg, offset = decode_regaddr(encoded)
        if reg > _SP:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)

        if reg == _SP:
            base = self.regs.sp
        else:
            base = self.regs.read(reg)

        page_offset = base + offset
        if page_offset < 0 or page_offset >= Memory.PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)

        if reg == _SP:
            return page_offset
        return self.regs.dp * Memory.PAGE_SIZE + page_offset

    # ── Register validation ────────────────────────────────────────────

    def _decode_gpr(self, code: int) -> int:
        if code > 3:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        return code

    def _decode_gpr_or_sp(self, code: int) -> int:
        if code > _SP:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        return code

    def _decode_mov_reg(self, code: int) -> int:
        if code > _DP:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        return code

    # ── Source resolvers ───────────────────────────────────────────────

    def _src_regaddr(self, insn: DecodedInsn) -> int:
        addr = self._indirect_addr(insn.operands[1])
        return self.mem[addr]

    def _src_addr(self, insn: DecodedInsn) -> int:
        addr = self._direct_addr(insn.operands[1])
        return self.mem[addr]

    def _src_const(self, insn: DecodedInsn) -> int:
        return insn.operands[1]

    def _src_stk_reg(self, insn: DecodedInsn) -> int:
        code = self._decode_gpr_or_sp(insn.operands[1])
        return self.regs.read(code)

    def _src_gpr_reg(self, insn: DecodedInsn) -> int:
        code = self._decode_gpr(insn.operands[1])
        return self.regs.read(code)

    def _src_muldiv_reg(self, insn: DecodedInsn) -> int:
        code = self._decode_gpr(insn.operands[0])
        return self.regs.read(code)

    def _src_muldiv_regaddr(self, insn: DecodedInsn) -> int:
        addr = self._indirect_addr(insn.operands[0])
        return self.mem[addr]

    def _src_muldiv_addr(self, insn: DecodedInsn) -> int:
        addr = self._direct_addr(insn.operands[0])
        return self.mem[addr]

    def _src_muldiv_const(self, insn: DecodedInsn) -> int:
        return insn.operands[0]

    # ── Stack helpers ──────────────────────────────────────────────────

    def _do_push(self, value: int) -> None:
        if self.regs.sp == 0:
            raise CpuFault(ErrorCode.STACK_OVERFLOW, self.regs.ip)
        self.mem[self.regs.sp] = value
        self.regs.sp -= 1

    def _do_pop(self) -> int:
        if self.regs.sp >= Memory.SP_INIT:
            raise CpuFault(ErrorCode.STACK_UNDERFLOW, self.regs.ip)
        self.regs.sp += 1
        return self.mem[self.regs.sp]

    # ── Dispatch table construction ────────────────────────────────────

    def _build_dispatch(self) -> None:
        d = self._dispatch

        # -- MOV variants --
        d[Op.MOV_REG_REG] = self._h_mov_reg_reg
        d[Op.MOV_REG_ADDR] = self._h_mov_reg_addr
        d[Op.MOV_REG_REGADDR] = self._h_mov_reg_regaddr
        d[Op.MOV_ADDR_REG] = self._h_mov_addr_reg
        d[Op.MOV_REGADDR_REG] = self._h_mov_regaddr_reg
        d[Op.MOV_REG_CONST] = self._h_mov_reg_const
        d[Op.MOV_ADDR_CONST] = self._h_mov_addr_const
        d[Op.MOV_REGADDR_CONST] = self._h_mov_regaddr_const

        # -- Arithmetic: ADD/SUB (4 variants each) --
        # Opcodes within each group are numerically contiguous: +0=REG, +1=REGADDR, +2=ADDR, +3=CONST
        for base, alu_fn in [(Op.ADD_REG_REG, ALU.add), (Op.SUB_REG_REG, ALU.sub)]:
            d[Op(base + 0)] = self._make_alu_2op(alu_fn, self._src_stk_reg)
            d[Op(base + 1)] = self._make_alu_2op(alu_fn, self._src_regaddr)
            d[Op(base + 2)] = self._make_alu_2op(alu_fn, self._src_addr)
            d[Op(base + 3)] = self._make_alu_2op(alu_fn, self._src_const)

        # -- INC / DEC --
        d[Op.INC_REG] = self._h_inc
        d[Op.DEC_REG] = self._h_dec

        # -- CMP (4 variants) --
        d[Op.CMP_REG_REG] = self._make_alu_2op(ALU.sub, self._src_stk_reg, writeback=False)
        d[Op.CMP_REG_REGADDR] = self._make_alu_2op(ALU.sub, self._src_regaddr, writeback=False)
        d[Op.CMP_REG_ADDR] = self._make_alu_2op(ALU.sub, self._src_addr, writeback=False)
        d[Op.CMP_REG_CONST] = self._make_alu_2op(ALU.sub, self._src_const, writeback=False)

        # -- JMP --
        d[Op.JMP_REG] = self._h_jmp_reg
        d[Op.JMP_ADDR] = self._h_jmp_addr

        # -- Conditional jumps (6 conditions x 2 forms) --
        d[Op.JC_REG] = self._make_jcc(lambda: self.regs.flags.c, is_reg=True)
        d[Op.JC_ADDR] = self._make_jcc(lambda: self.regs.flags.c, is_reg=False)
        d[Op.JNC_REG] = self._make_jcc(lambda: not self.regs.flags.c, is_reg=True)
        d[Op.JNC_ADDR] = self._make_jcc(lambda: not self.regs.flags.c, is_reg=False)
        d[Op.JZ_REG] = self._make_jcc(lambda: self.regs.flags.z, is_reg=True)
        d[Op.JZ_ADDR] = self._make_jcc(lambda: self.regs.flags.z, is_reg=False)
        d[Op.JNZ_REG] = self._make_jcc(lambda: not self.regs.flags.z, is_reg=True)
        d[Op.JNZ_ADDR] = self._make_jcc(lambda: not self.regs.flags.z, is_reg=False)
        d[Op.JA_REG] = self._make_jcc(
            lambda: not self.regs.flags.c and not self.regs.flags.z, is_reg=True)
        d[Op.JA_ADDR] = self._make_jcc(
            lambda: not self.regs.flags.c and not self.regs.flags.z, is_reg=False)
        d[Op.JNA_REG] = self._make_jcc(
            lambda: self.regs.flags.c or self.regs.flags.z, is_reg=True)
        d[Op.JNA_ADDR] = self._make_jcc(
            lambda: self.regs.flags.c or self.regs.flags.z, is_reg=False)

        # -- PUSH (4 variants) --
        d[Op.PUSH_REG] = self._h_push_reg
        d[Op.PUSH_REGADDR] = self._h_push_regaddr
        d[Op.PUSH_ADDR] = self._h_push_addr
        d[Op.PUSH_CONST] = self._h_push_const

        # -- POP --
        d[Op.POP_REG] = self._h_pop_reg

        # -- CALL / RET --
        d[Op.CALL_REG] = self._h_call_reg
        d[Op.CALL_ADDR] = self._h_call_addr
        d[Op.RET] = self._h_ret

        # -- MUL (4 variants) --
        d[Op.MUL_REG] = self._make_muldiv(ALU.mul, self._src_muldiv_reg)
        d[Op.MUL_REGADDR] = self._make_muldiv(ALU.mul, self._src_muldiv_regaddr)
        d[Op.MUL_ADDR] = self._make_muldiv(ALU.mul, self._src_muldiv_addr)
        d[Op.MUL_CONST] = self._make_muldiv(ALU.mul, self._src_muldiv_const)

        # -- DIV (4 variants) --
        d[Op.DIV_REG] = self._make_div(self._src_muldiv_reg)
        d[Op.DIV_REGADDR] = self._make_div(self._src_muldiv_regaddr)
        d[Op.DIV_ADDR] = self._make_div(self._src_muldiv_addr)
        d[Op.DIV_CONST] = self._make_div(self._src_muldiv_const)

        # -- Bitwise: AND/OR/XOR (4 variants each) --
        for base, alu_fn in [
            (Op.AND_REG_REG, ALU.and_op),
            (Op.OR_REG_REG, ALU.or_op),
            (Op.XOR_REG_REG, ALU.xor_op),
        ]:
            d[Op(base + 0)] = self._make_bitwise_2op(alu_fn, self._src_gpr_reg)
            d[Op(base + 1)] = self._make_bitwise_2op(alu_fn, self._src_regaddr)
            d[Op(base + 2)] = self._make_bitwise_2op(alu_fn, self._src_addr)
            d[Op(base + 3)] = self._make_bitwise_2op(alu_fn, self._src_const)

        # -- NOT --
        d[Op.NOT_REG] = self._h_not

        # -- Shift: SHL/SHR (4 variants each) --
        for base, alu_fn in [(Op.SHL_REG_REG, ALU.shl), (Op.SHR_REG_REG, ALU.shr)]:
            d[Op(base + 0)] = self._make_shift_2op(alu_fn, self._src_gpr_reg)
            d[Op(base + 1)] = self._make_shift_2op(alu_fn, self._src_regaddr)
            d[Op(base + 2)] = self._make_shift_2op(alu_fn, self._src_addr)
            d[Op(base + 3)] = self._make_shift_2op(alu_fn, self._src_const)

        # Completeness check: every integer Op except HLT must have a
        # handler.  FP opcodes (BY_CODE_FP) are handled separately.
        _fp_ops = {Op(c) for c in BY_CODE_FP}
        missing = (
            {op for op in Op if op != Op.HLT} - _fp_ops - set(d)
        )
        if missing:
            names = ", ".join(sorted(op.name for op in missing))
            raise RuntimeError(f"Dispatch table missing handlers: {names}")

    # ── Handler factories ──────────────────────────────────────────────

    def _make_alu_2op(
        self,
        alu_fn: Callable[[int, int], tuple[int, bool, bool]],
        resolve_src: Callable[[DecodedInsn], int],
        *,
        writeback: bool = True,
    ) -> Handler:
        """Create handler for 2-operand ALU instructions (ADD/SUB/CMP)."""
        def handler(insn: DecodedInsn) -> None:
            dest_code = self._decode_gpr_or_sp(insn.operands[0])
            right = resolve_src(insn)
            left = self.regs.read(dest_code)
            result, carry, zero = alu_fn(left, right)
            self.regs.flags.c = carry
            self.regs.flags.z = zero
            if writeback:
                self.regs.write(dest_code, result)
            self.regs.ip += insn.size
        return handler

    def _make_bitwise_2op(
        self,
        alu_fn: Callable[[int, int], tuple[int, bool]],
        resolve_src: Callable[[DecodedInsn], int],
    ) -> Handler:
        """Create handler for 2-operand bitwise instructions (AND/OR/XOR)."""
        def handler(insn: DecodedInsn) -> None:
            dest_code = self._decode_gpr(insn.operands[0])
            right = resolve_src(insn)
            left = self.regs.read(dest_code)
            result, zero = alu_fn(left, right)
            self.regs.flags.c = False
            self.regs.flags.z = zero
            self.regs.write(dest_code, result)
            self.regs.ip += insn.size
        return handler

    def _make_shift_2op(
        self,
        alu_fn: Callable[[int, int], tuple[int, bool, bool]],
        resolve_src: Callable[[DecodedInsn], int],
    ) -> Handler:
        """Create handler for 2-operand shift instructions (SHL/SHR)."""
        def handler(insn: DecodedInsn) -> None:
            dest_code = self._decode_gpr(insn.operands[0])
            count = resolve_src(insn)
            value = self.regs.read(dest_code)
            if count == 0:
                # Spec: when count==0, value unchanged, C unchanged, Z updated
                self.regs.flags.z = value == 0
            else:
                result, carry, zero = alu_fn(value, count)
                self.regs.flags.c = carry
                self.regs.flags.z = zero
                self.regs.write(dest_code, result)
            self.regs.ip += insn.size
        return handler

    def _make_jcc(
        self,
        condition: Callable[[], bool],
        *,
        is_reg: bool,
    ) -> Handler:
        """Create handler for conditional jumps."""
        def handler(insn: DecodedInsn) -> None:
            if is_reg:
                code = self._decode_gpr(insn.operands[0])
                target = self.regs.read(code)
            else:
                target = insn.operands[0]
            if condition():
                self.regs.ip = target
            else:
                self.regs.ip += insn.size
        return handler

    def _make_muldiv(
        self,
        alu_fn: Callable[[int, int], tuple[int, bool, bool]],
        resolve_src: Callable[[DecodedInsn], int],
    ) -> Handler:
        """Create handler for MUL instructions (A = A * operand)."""
        def handler(insn: DecodedInsn) -> None:
            right = resolve_src(insn)
            result, carry, zero = alu_fn(self.regs.a, right)
            self.regs.flags.c = carry
            self.regs.flags.z = zero
            self.regs.a = result
            self.regs.ip += insn.size
        return handler

    def _make_div(
        self,
        resolve_src: Callable[[DecodedInsn], int],
    ) -> Handler:
        """Create handler for DIV instructions (A = A / operand)."""
        def handler(insn: DecodedInsn) -> None:
            right = resolve_src(insn)
            if right == 0:
                raise CpuFault(ErrorCode.DIV_ZERO, self.regs.ip)
            result, carry, zero = ALU.div(self.regs.a, right)
            self.regs.flags.c = carry
            self.regs.flags.z = zero
            self.regs.a = result
            self.regs.ip += insn.size
        return handler

    # ── Individual handlers ────────────────────────────────────────────

    # -- MOV --

    def _h_mov_reg_reg(self, insn: DecodedInsn) -> None:
        dest = self._decode_mov_reg(insn.operands[0])
        src = self._decode_mov_reg(insn.operands[1])
        val = self.regs.read(src)
        self.regs.write(dest, val)
        self.regs.ip += insn.size

    def _h_mov_reg_addr(self, insn: DecodedInsn) -> None:
        dest = self._decode_mov_reg(insn.operands[0])
        addr = self._direct_addr(insn.operands[1])
        val = self.mem[addr]
        self.regs.write(dest, val)
        self.regs.ip += insn.size

    def _h_mov_reg_regaddr(self, insn: DecodedInsn) -> None:
        dest = self._decode_mov_reg(insn.operands[0])
        addr = self._indirect_addr(insn.operands[1])
        val = self.mem[addr]
        self.regs.write(dest, val)
        self.regs.ip += insn.size

    def _h_mov_addr_reg(self, insn: DecodedInsn) -> None:
        addr = self._direct_addr(insn.operands[0])
        src = self._decode_mov_reg(insn.operands[1])
        val = self.regs.read(src)
        self.mem[addr] = val
        self.regs.ip += insn.size

    def _h_mov_regaddr_reg(self, insn: DecodedInsn) -> None:
        addr = self._indirect_addr(insn.operands[0])
        src = self._decode_mov_reg(insn.operands[1])
        val = self.regs.read(src)
        self.mem[addr] = val
        self.regs.ip += insn.size

    def _h_mov_reg_const(self, insn: DecodedInsn) -> None:
        dest = self._decode_mov_reg(insn.operands[0])
        val = insn.operands[1]
        self.regs.write(dest, val)
        self.regs.ip += insn.size

    def _h_mov_addr_const(self, insn: DecodedInsn) -> None:
        addr = self._direct_addr(insn.operands[0])
        val = insn.operands[1]
        self.mem[addr] = val
        self.regs.ip += insn.size

    def _h_mov_regaddr_const(self, insn: DecodedInsn) -> None:
        addr = self._indirect_addr(insn.operands[0])
        val = insn.operands[1]
        self.mem[addr] = val
        self.regs.ip += insn.size

    # -- INC / DEC --

    def _h_inc(self, insn: DecodedInsn) -> None:
        code = self._decode_gpr_or_sp(insn.operands[0])
        val = self.regs.read(code)
        result, carry, zero = ALU.inc(val)
        self.regs.flags.c = carry
        self.regs.flags.z = zero
        self.regs.write(code, result)
        self.regs.ip += insn.size

    def _h_dec(self, insn: DecodedInsn) -> None:
        code = self._decode_gpr_or_sp(insn.operands[0])
        val = self.regs.read(code)
        result, carry, zero = ALU.dec(val)
        self.regs.flags.c = carry
        self.regs.flags.z = zero
        self.regs.write(code, result)
        self.regs.ip += insn.size

    # -- JMP --

    def _h_jmp_reg(self, insn: DecodedInsn) -> None:
        code = self._decode_gpr(insn.operands[0])
        self.regs.ip = self.regs.read(code)

    def _h_jmp_addr(self, insn: DecodedInsn) -> None:
        self.regs.ip = insn.operands[0]

    # -- PUSH --

    def _h_push_reg(self, insn: DecodedInsn) -> None:
        code = self._decode_gpr(insn.operands[0])
        val = self.regs.read(code)
        self._do_push(val)
        self.regs.ip += insn.size

    def _h_push_regaddr(self, insn: DecodedInsn) -> None:
        addr = self._indirect_addr(insn.operands[0])
        val = self.mem[addr]
        self._do_push(val)
        self.regs.ip += insn.size

    def _h_push_addr(self, insn: DecodedInsn) -> None:
        addr = self._direct_addr(insn.operands[0])
        val = self.mem[addr]
        self._do_push(val)
        self.regs.ip += insn.size

    def _h_push_const(self, insn: DecodedInsn) -> None:
        val = insn.operands[0]
        self._do_push(val)
        self.regs.ip += insn.size

    # -- POP --

    def _h_pop_reg(self, insn: DecodedInsn) -> None:
        code = self._decode_gpr(insn.operands[0])
        val = self._do_pop()
        self.regs.write(code, val)
        self.regs.ip += insn.size

    # -- CALL / RET --

    def _h_call_reg(self, insn: DecodedInsn) -> None:
        code = self._decode_gpr(insn.operands[0])
        target = self.regs.read(code)
        return_addr = self.regs.ip + insn.size
        self._do_push(return_addr)
        self.regs.ip = target

    def _h_call_addr(self, insn: DecodedInsn) -> None:
        target = insn.operands[0]
        return_addr = self.regs.ip + insn.size
        self._do_push(return_addr)
        self.regs.ip = target

    def _h_ret(self, insn: DecodedInsn) -> None:
        self.regs.ip = self._do_pop()

    # -- NOT --

    def _h_not(self, insn: DecodedInsn) -> None:
        code = self._decode_gpr(insn.operands[0])
        val = self.regs.read(code)
        result, zero = ALU.not_op(val)
        self.regs.flags.c = False
        self.regs.flags.z = zero
        self.regs.write(code, result)
        self.regs.ip += insn.size
