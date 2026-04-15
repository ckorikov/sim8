"""Instruction handlers: dispatch table, address resolution, factories."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

from pysim8.isa import BY_CODE_FP, BY_CODE_VU, Op, Reg, decode_regaddr

from ._dispatch_config import DISPATCH_CONFIG
from .alu import ALU
from .decoder import DecodedInstr
from .errors import CpuFault, ErrorCode
from .memory import PAGE_SIZE, SP_INIT, Memory

if TYPE_CHECKING:
    from .registers import RegisterFile

_D = Reg.D
_SP = Reg.SP
_DP = Reg.DP

__all__ = ["HandlersMixin", "Handler"]

type Handler = Callable[[DecodedInstr], None]


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
        return self.regs.dp * PAGE_SIZE + offset

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
        if page_offset < 0 or page_offset >= PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)

        if reg == _SP:
            return page_offset
        return self.regs.dp * PAGE_SIZE + page_offset

    # ── Register validation ────────────────────────────────────────────

    def _decode_gpr(self, code: int) -> int:
        if code > _D:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        return code

    def _decode_gpr_or_sp(self, code: int) -> int:
        if code > _SP:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        return code

    def _decode_gpr_or_dp(self, code: int) -> int:
        if code > _D and code != _DP:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        return code

    def _decode_mov_reg(self, code: int) -> int:
        if code > _DP:
            raise CpuFault(ErrorCode.INVALID_REG, self.regs.ip)
        return code

    # ── Source resolvers ───────────────────────────────────────────────

    def _src_regaddr(self, instr: DecodedInstr) -> int:
        addr = self._indirect_addr(instr.operands[1])
        return self.mem[addr]

    def _src_addr(self, instr: DecodedInstr) -> int:
        addr = self._direct_addr(instr.operands[1])
        return self.mem[addr]

    def _src_const(self, instr: DecodedInstr) -> int:
        return instr.operands[1]

    def _src_stk_reg(self, instr: DecodedInstr) -> int:
        code = self._decode_gpr_or_sp(instr.operands[1])
        return self.regs.read(code)

    def _src_gpr_reg(self, instr: DecodedInstr) -> int:
        code = self._decode_gpr(instr.operands[1])
        return self.regs.read(code)

    def _src_muldiv_reg(self, instr: DecodedInstr) -> int:
        code = self._decode_gpr(instr.operands[0])
        return self.regs.read(code)

    def _src_muldiv_regaddr(self, instr: DecodedInstr) -> int:
        addr = self._indirect_addr(instr.operands[0])
        return self.mem[addr]

    def _src_muldiv_addr(self, instr: DecodedInstr) -> int:
        addr = self._direct_addr(instr.operands[0])
        return self.mem[addr]

    def _src_muldiv_const(self, instr: DecodedInstr) -> int:
        return instr.operands[0]

    # ── Unary ALU helpers ──────────────────────────────────────────────

    def _apply_unary_alu(
        self,
        instr: DecodedInstr,
        alu_fn: Callable[[int], tuple[int, bool, bool]],
    ) -> None:
        """Apply a unary ALU op (INC/DEC) to a GPR-or-SP register: update C and Z."""
        code = self._decode_gpr_or_sp(instr.operands[0])
        result, carry, zero = alu_fn(self.regs.read(code))
        self.regs.flags.c = carry
        self.regs.flags.z = zero
        self.regs.write(code, result)
        self.regs.ip += instr.size

    def _apply_gpr_bitwise_unary(
        self,
        instr: DecodedInstr,
        alu_fn: Callable[[int], tuple[int, bool]],
    ) -> None:
        """Apply a bitwise unary op (NOT) to a GPR: always clears C, updates Z."""
        code = self._decode_gpr(instr.operands[0])
        result, zero = alu_fn(self.regs.read(code))
        self.regs.flags.c = False
        self.regs.flags.z = zero
        self.regs.write(code, result)
        self.regs.ip += instr.size

    # ── Stack helpers ──────────────────────────────────────────────────

    def _do_push(self, value: int) -> None:
        if self.regs.sp == 0:
            raise CpuFault(ErrorCode.STACK_OVERFLOW, self.regs.ip)
        self.mem[self.regs.sp] = value
        self.regs.sp -= 1

    def _do_pop(self) -> int:
        if self.regs.sp >= SP_INIT:
            raise CpuFault(ErrorCode.STACK_UNDERFLOW, self.regs.ip)
        self.regs.sp += 1
        return self.mem[self.regs.sp]

    def _do_call(self, target: int, return_addr: int) -> None:
        """Push return address onto stack and jump to target."""
        self._do_push(return_addr)
        self.regs.ip = target

    # ── Dispatch table construction ────────────────────────────────────

    def _build_dispatch(self) -> None:
        d = self._dispatch
        _alu = {
            "add": ALU.add,
            "sub": ALU.sub,
            "mul": ALU.mul,
            "and": ALU.and_op,
            "or": ALU.or_op,
            "xor": ALU.xor_op,
            "shl": ALU.shl,
            "shr": ALU.shr,
        }
        _src = {
            "stk_reg": self._src_stk_reg,
            "regaddr": self._src_regaddr,
            "addr": self._src_addr,
            "const": self._src_const,
            "gpr_reg": self._src_gpr_reg,
            "muldiv_reg": self._src_muldiv_reg,
            "muldiv_regaddr": self._src_muldiv_regaddr,
            "muldiv_addr": self._src_muldiv_addr,
            "muldiv_const": self._src_muldiv_const,
        }
        _jcc: dict[str, Callable[[], bool]] = {
            "c": lambda: self.regs.flags.c,
            "nc": lambda: not self.regs.flags.c,
            "z": lambda: self.regs.flags.z,
            "nz": lambda: not self.regs.flags.z,
            "a": lambda: not self.regs.flags.c and not self.regs.flags.z,
            "na": lambda: self.regs.flags.c or self.regs.flags.z,
        }
        for entry in DISPATCH_CONFIG:
            op, typ = entry[0], entry[1]
            match typ:
                case "direct":
                    d[op] = getattr(self, entry[2])
                case "alu_2op":
                    d[op] = self._make_alu_2op(_alu[entry[2]], _src[entry[3]])
                case "alu_2op_no_wb":
                    d[op] = self._make_alu_2op(_alu[entry[2]], _src[entry[3]], writeback=False)
                case "bitwise":
                    d[op] = self._make_bitwise_2op(_alu[entry[2]], _src[entry[3]])
                case "shift":
                    d[op] = self._make_shift_2op(_alu[entry[2]], _src[entry[3]])
                case "muldiv":
                    d[op] = self._make_muldiv(_alu[entry[2]], _src[entry[3]])
                case "div":
                    d[op] = self._make_div(_src[entry[2]])
                case "jcc":
                    d[op] = self._make_jcc(_jcc[entry[2]], is_reg=entry[3] == "reg")
        self._validate_dispatch_complete(d)

    @staticmethod
    def _validate_dispatch_complete(d: dict[Op, Handler]) -> None:
        """Verify every non-HLT, non-FP Op has a handler."""
        _fp_ops: set[Op] = {Op(c) for c in BY_CODE_FP}
        _vu_ops: set[Op] = {Op(c) for c in BY_CODE_VU}
        all_ops: set[Op] = {op for op in Op if op != Op.HLT}
        missing = all_ops - _fp_ops - _vu_ops - set(d)
        if missing:
            names = ", ".join(sorted(op.name for op in missing))
            raise RuntimeError(f"Dispatch table missing handlers: {names}")

    # ── Handler factories ──────────────────────────────────────────────

    def _apply_alu_2op(
        self,
        instr: DecodedInstr,
        alu_fn: Callable[[int, int], tuple[int, bool, bool]],
        resolve_src: Callable[[DecodedInstr], int],
        *,
        writeback: bool = True,
    ) -> None:
        """Apply a 2-operand ALU op (ADD/SUB/CMP): update C and Z flags, optionally write back."""
        dest_code = self._decode_gpr_or_sp(instr.operands[0])
        result, carry, zero = alu_fn(self.regs.read(dest_code), resolve_src(instr))
        self.regs.flags.c = carry
        self.regs.flags.z = zero
        if writeback:
            self.regs.write(dest_code, result)
        self.regs.ip += instr.size

    def _apply_bitwise_2op(
        self,
        instr: DecodedInstr,
        alu_fn: Callable[[int, int], tuple[int, bool]],
        resolve_src: Callable[[DecodedInstr], int],
    ) -> None:
        """Apply a 2-operand bitwise op (AND/OR/XOR): always clears C, updates Z."""
        dest_code = self._decode_gpr(instr.operands[0])
        result, zero = alu_fn(self.regs.read(dest_code), resolve_src(instr))
        self.regs.flags.c = False
        self.regs.flags.z = zero
        self.regs.write(dest_code, result)
        self.regs.ip += instr.size

    def _apply_shift_2op(
        self,
        instr: DecodedInstr,
        alu_fn: Callable[[int, int], tuple[int, bool, bool]],
        resolve_src: Callable[[DecodedInstr], int],
    ) -> None:
        """Apply a 2-operand shift (SHL/SHR): count==0 only updates Z; otherwise updates C, Z, and writes back."""
        dest_code = self._decode_gpr(instr.operands[0])
        count = resolve_src(instr)
        value = self.regs.read(dest_code)
        if count == 0:
            # Spec: when count==0, value unchanged, C unchanged, Z updated
            self.regs.flags.z = value == 0
        else:
            result, carry, zero = alu_fn(value, count)
            self.regs.flags.c = carry
            self.regs.flags.z = zero
            self.regs.write(dest_code, result)
        self.regs.ip += instr.size

    def _apply_jcc(self, instr: DecodedInstr, condition: Callable[[], bool], *, is_reg: bool) -> None:
        """Evaluate condition and jump to target or advance IP."""
        if is_reg:
            target = self.regs.read(self._decode_gpr(instr.operands[0]))
        else:
            target = instr.operands[0]
        if condition():
            self.regs.ip = target
        else:
            self.regs.ip += instr.size

    def _apply_muldiv(
        self,
        instr: DecodedInstr,
        alu_fn: Callable[[int, int], tuple[int, bool, bool]],
        resolve_src: Callable[[DecodedInstr], int],
    ) -> None:
        """Apply MUL: A = A * operand, update C and Z."""
        result, carry, zero = alu_fn(self.regs.a, resolve_src(instr))
        self.regs.flags.c = carry
        self.regs.flags.z = zero
        self.regs.a = result
        self.regs.ip += instr.size

    def _apply_div(self, instr: DecodedInstr, resolve_src: Callable[[DecodedInstr], int]) -> None:
        """Apply DIV: A = A / operand. Raises FAULT on zero divisor."""
        right = resolve_src(instr)
        if right == 0:
            raise CpuFault(ErrorCode.DIV_ZERO, self.regs.ip)
        result, carry, zero = ALU.div(self.regs.a, right)
        self.regs.flags.c = carry
        self.regs.flags.z = zero
        self.regs.a = result
        self.regs.ip += instr.size

    def _make_alu_2op(
        self,
        alu_fn: Callable[[int, int], tuple[int, bool, bool]],
        resolve_src: Callable[[DecodedInstr], int],
        *,
        writeback: bool = True,
    ) -> Handler:
        return lambda instr: self._apply_alu_2op(instr, alu_fn, resolve_src, writeback=writeback)

    def _make_bitwise_2op(
        self, alu_fn: Callable[[int, int], tuple[int, bool]], resolve_src: Callable[[DecodedInstr], int]
    ) -> Handler:
        return lambda instr: self._apply_bitwise_2op(instr, alu_fn, resolve_src)

    def _make_shift_2op(
        self, alu_fn: Callable[[int, int], tuple[int, bool, bool]], resolve_src: Callable[[DecodedInstr], int]
    ) -> Handler:
        return lambda instr: self._apply_shift_2op(instr, alu_fn, resolve_src)

    def _make_jcc(self, condition: Callable[[], bool], *, is_reg: bool) -> Handler:
        return lambda instr: self._apply_jcc(instr, condition, is_reg=is_reg)

    def _make_muldiv(
        self, alu_fn: Callable[[int, int], tuple[int, bool, bool]], resolve_src: Callable[[DecodedInstr], int]
    ) -> Handler:
        return lambda instr: self._apply_muldiv(instr, alu_fn, resolve_src)

    def _make_div(self, resolve_src: Callable[[DecodedInstr], int]) -> Handler:
        return lambda instr: self._apply_div(instr, resolve_src)

    # ── Individual handlers ────────────────────────────────────────────

    # -- MOV --

    def _mov_reg_from_mem(self, instr: DecodedInstr, addr: int) -> None:
        """Load byte from memory address into destination register."""
        self.regs.write(self._decode_mov_reg(instr.operands[0]), self.mem[addr])
        self.regs.ip += instr.size

    def _mov_mem_from_reg(self, instr: DecodedInstr, addr: int) -> None:
        """Store source register value to memory address."""
        self.mem[addr] = self.regs.read(self._decode_mov_reg(instr.operands[1]))
        self.regs.ip += instr.size

    def _mov_mem_const(self, instr: DecodedInstr, addr: int) -> None:
        """Store immediate constant to memory address."""
        self.mem[addr] = instr.operands[1]
        self.regs.ip += instr.size

    def _h_mov_reg_reg(self, instr: DecodedInstr) -> None:
        self.regs.write(
            self._decode_mov_reg(instr.operands[0]), self.regs.read(self._decode_mov_reg(instr.operands[1]))
        )
        self.regs.ip += instr.size

    def _h_mov_reg_addr(self, instr: DecodedInstr) -> None:
        self._mov_reg_from_mem(instr, self._direct_addr(instr.operands[1]))

    def _h_mov_reg_regaddr(self, instr: DecodedInstr) -> None:
        self._mov_reg_from_mem(instr, self._indirect_addr(instr.operands[1]))

    def _h_mov_addr_reg(self, instr: DecodedInstr) -> None:
        self._mov_mem_from_reg(instr, self._direct_addr(instr.operands[0]))

    def _h_mov_regaddr_reg(self, instr: DecodedInstr) -> None:
        self._mov_mem_from_reg(instr, self._indirect_addr(instr.operands[0]))

    def _h_mov_reg_const(self, instr: DecodedInstr) -> None:
        self.regs.write(self._decode_mov_reg(instr.operands[0]), instr.operands[1])
        self.regs.ip += instr.size

    def _h_mov_addr_const(self, instr: DecodedInstr) -> None:
        self._mov_mem_const(instr, self._direct_addr(instr.operands[0]))

    def _h_mov_regaddr_const(self, instr: DecodedInstr) -> None:
        self._mov_mem_const(instr, self._indirect_addr(instr.operands[0]))

    # -- INC / DEC --

    def _h_inc(self, instr: DecodedInstr) -> None:
        self._apply_unary_alu(instr, ALU.inc)

    def _h_dec(self, instr: DecodedInstr) -> None:
        self._apply_unary_alu(instr, ALU.dec)

    # -- JMP --

    def _h_jmp_reg(self, instr: DecodedInstr) -> None:
        code = self._decode_gpr(instr.operands[0])
        self.regs.ip = self.regs.read(code)

    def _h_jmp_addr(self, instr: DecodedInstr) -> None:
        self.regs.ip = instr.operands[0]

    # -- PUSH --

    def _push_and_advance(self, instr: DecodedInstr, value: int) -> None:
        """Push value onto stack and advance IP."""
        self._do_push(value)
        self.regs.ip += instr.size

    def _h_push_reg(self, instr: DecodedInstr) -> None:
        self._push_and_advance(instr, self.regs.read(self._decode_gpr_or_dp(instr.operands[0])))

    def _h_push_regaddr(self, instr: DecodedInstr) -> None:
        self._push_and_advance(instr, self.mem[self._indirect_addr(instr.operands[0])])

    def _h_push_addr(self, instr: DecodedInstr) -> None:
        self._push_and_advance(instr, self.mem[self._direct_addr(instr.operands[0])])

    def _h_push_const(self, instr: DecodedInstr) -> None:
        self._push_and_advance(instr, instr.operands[0])

    # -- POP --

    def _h_pop_reg(self, instr: DecodedInstr) -> None:
        code = self._decode_gpr_or_dp(instr.operands[0])
        val = self._do_pop()
        self.regs.write(code, val)
        self.regs.ip += instr.size

    # -- CALL / RET --

    def _h_call_reg(self, instr: DecodedInstr) -> None:
        self._do_call(
            target=self.regs.read(self._decode_gpr(instr.operands[0])),
            return_addr=self.regs.ip + instr.size,
        )

    def _h_call_addr(self, instr: DecodedInstr) -> None:
        self._do_call(target=instr.operands[0], return_addr=self.regs.ip + instr.size)

    def _h_ret(self, instr: DecodedInstr) -> None:
        self.regs.ip = self._do_pop()

    # -- NOT --

    def _h_not(self, instr: DecodedInstr) -> None:
        self._apply_gpr_bitwise_unary(instr, ALU.not_op)
