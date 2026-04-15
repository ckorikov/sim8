"""FP instruction handlers for the CPU simulator."""

from __future__ import annotations

import math
from collections.abc import Callable
from typing import TYPE_CHECKING

from pysim8.fp_arithmetic import (
    fp_abs,
    fp_add,
    fp_classify,
    fp_cmp,
    fp_div,
    fp_mul,
    fp_neg,
    fp_sqrt,
    fp_sub,
)
from pysim8.fp_formats import (
    FpExceptions,
    RoundingMode,
    bytes_to_float,
    float_to_bytes,
)
from pysim8.isa import (
    FP_FMT_BF,
    FP_FMT_H,
    FP_FMT_O2,
    FP_FMT_O3,
    FP_FMT_WIDTH,
    Op,
    decode_fpm,
    validate_fpm,
)

from .decoder import DecodedInstr
from .errors import CpuFault, ErrorCode
from .memory import PAGE_SIZE, Memory

# Maps rounding mode to the corresponding float→int conversion function.
_RM_ROUND_FN: dict[int, Callable[[float], int]] = {
    RoundingMode.RNE: round,
    RoundingMode.RTZ: int,
    RoundingMode.RDN: math.floor,
    RoundingMode.RUP: math.ceil,
}

if TYPE_CHECKING:
    from .handlers import Handler
    from .registers import FpuRegisters, RegisterFile

__all__ = ["HandlersFpMixin"]


class HandlersFpMixin:
    """Mixin providing FP instruction handlers for CPU.

    Expects: self.mem, self.regs (with .fpu), self._dispatch,
    self._direct_addr, self._indirect_addr, self._decode_gpr.
    """

    mem: Memory
    regs: RegisterFile
    _dispatch: dict[Op, Handler]

    def _direct_addr(self, offset: int) -> int:
        raise NotImplementedError

    def _indirect_addr(self, encoded: int) -> int:
        raise NotImplementedError

    def _decode_gpr(self, code: int) -> int:
        raise NotImplementedError

    # ── FPU access ─────────────────────────────────────────────────

    @property
    def _fpu(self) -> FpuRegisters:
        fpu = self.regs.fpu
        if fpu is None:
            raise RuntimeError("FPU not available (arch < 2)")
        return fpu

    def _validate_fpm(self, fpm: int) -> tuple[int, int, int]:
        """Validate FPM byte, return (phys, pos, fmt).

        Raises FAULT(FP_FORMAT) on invalid encoding.
        """
        if not validate_fpm(fpm):
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)
        return decode_fpm(fpm)

    def _validate_two_fpm_same_fmt(
        self,
        instr: DecodedInstr,
    ) -> tuple[int, int, int, int, int, int]:
        """Validate operands[0] and operands[1] as FPMs with matching format.

        Returns (dst_phys, dst_pos, dst_fmt, src_phys, src_pos, src_fmt).
        Raises FAULT(FP_FORMAT) on invalid encoding or format mismatch.
        """
        dst_phys, dst_pos, dst_fmt = self._validate_fpm(instr.operands[0])
        src_phys, src_pos, src_fmt = self._validate_fpm(instr.operands[1])
        if dst_fmt != src_fmt:
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)
        return dst_phys, dst_pos, dst_fmt, src_phys, src_pos, src_fmt

    # ── FP operation helpers ───────────────────────────────────────

    @staticmethod
    def _fp_merge_exc(e1: FpExceptions, e2: FpExceptions) -> FpExceptions:
        """Combine two FpExceptions by OR-ing each flag."""
        return FpExceptions(
            invalid=e1.invalid or e2.invalid,
            div_zero=e1.div_zero or e2.div_zero,
            overflow=e1.overflow or e2.overflow,
            underflow=e1.underflow or e2.underflow,
            inexact=e1.inexact or e2.inexact,
        )

    def _fp_apply_cmp(self, a: float, b: float) -> None:
        """FP compare: accumulate exceptions, update Z and C flags."""
        z, c, exc = fp_cmp(a, b)
        self._fpu.accumulate_exceptions(exc)
        self.regs.flags.z = z
        self.regs.flags.c = c

    def _fp_read_reg_and_raw(self, pos: int, fmt: int, phys: int) -> tuple[float, int]:
        """Read FP register, returning (float_value, raw_bits)."""
        raw = self._fpu.read_bits(pos, fmt, phys)
        return bytes_to_float(raw.to_bytes(FP_FMT_WIDTH[fmt] // 8, "little"), fmt), raw

    # ── Memory helpers ─────────────────────────────────────────────

    def _validate_page_boundary(self, addr: int, nbytes: int) -> None:
        """Raise PAGE_BOUNDARY if [addr, addr+nbytes) crosses a page."""
        if addr % PAGE_SIZE + nbytes > PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)

    def _fp_read_mem_raw(self, addr: int, fmt: int) -> bytes:
        """Read raw bytes from memory for an FP value."""
        nbytes = FP_FMT_WIDTH[fmt] // 8
        self._validate_page_boundary(addr, nbytes)
        return bytes(self.mem[addr + i] for i in range(nbytes))

    def _fp_read_mem(self, addr: int, fmt: int) -> float:
        """Read FP value from memory (little-endian)."""
        return bytes_to_float(self._fp_read_mem_raw(addr, fmt), fmt)

    def _fp_write_mem_raw(self, addr: int, fmt: int, data: bytes) -> None:
        """Write raw bytes to memory."""
        self._validate_page_boundary(addr, FP_FMT_WIDTH[fmt] // 8)
        for i, b in enumerate(data):
            self.mem[addr + i] = b

    # ── Register helpers ───────────────────────────────────────────

    def _fp_read_reg(
        self,
        pos: int,
        fmt: int,
        phys: int = 0,
    ) -> float:
        """Read FP register as float value."""
        raw = self._fpu.read_bits(pos, fmt, phys)
        width = FP_FMT_WIDTH[fmt]
        data = raw.to_bytes(width // 8, "little")
        return bytes_to_float(data, fmt)

    def _fp_write_reg(
        self,
        pos: int,
        fmt: int,
        value: float,
        phys: int = 0,
    ) -> None:
        """Write float value to FP register (with rounding)."""
        data, exc = float_to_bytes(
            value,
            fmt,
            self._fpu.rounding_mode,
        )
        self._fpu.accumulate_exceptions(exc)
        raw = int.from_bytes(data, "little")
        self._fpu.write_bits(pos, fmt, raw, phys)

    # ── Dispatch registration ──────────────────────────────────────

    def _build_fp_dispatch(self) -> None:
        """Register all FP instruction handlers."""
        d = self._dispatch

        # FMOV (128-131, 161-162)
        d[Op.FMOV_FP_ADDR] = self._h_fp_load_direct
        d[Op.FMOV_FP_REGADDR] = self._h_fp_load_indirect
        d[Op.FMOV_ADDR_FP] = self._h_fp_store_direct
        d[Op.FMOV_REGADDR_FP] = self._h_fp_store_indirect
        d[Op.FMOV_FP_IMM8] = self._h_fp_write_imm8
        d[Op.FMOV_FP_IMM16] = self._h_fp_write_imm16

        # Arithmetic mem variants (132-141)
        for op_addr, op_regaddr, fn in [
            (Op.FADD_FP_ADDR, Op.FADD_FP_REGADDR, fp_add),
            (Op.FSUB_FP_ADDR, Op.FSUB_FP_REGADDR, fp_sub),
            (Op.FMUL_FP_ADDR, Op.FMUL_FP_REGADDR, fp_mul),
            (Op.FDIV_FP_ADDR, Op.FDIV_FP_REGADDR, fp_div),
        ]:
            d[op_addr] = self._make_fp_arith_mem(fn, self._direct_addr)
            d[op_regaddr] = self._make_fp_arith_mem(fn, self._indirect_addr)
        d[Op.FCMP_FP_ADDR] = self._make_fp_cmp_mem(self._direct_addr)
        d[Op.FCMP_FP_REGADDR] = self._make_fp_cmp_mem(self._indirect_addr)

        # Unary (142-144)
        d[Op.FABS_FP] = self._h_fp_abs
        d[Op.FNEG_FP] = self._h_fp_neg
        d[Op.FSQRT_FP] = self._h_fp_sqrt

        # FMOV reg-reg (145)
        d[Op.FMOV_RR] = self._h_fp_copy_reg

        # FCVT (146)
        d[Op.FCVT_FP_FP] = self._h_fp_convert_format

        # FITOF/FFTOI (147-148)
        d[Op.FITOF_FP_GPR] = self._h_fp_int_to_float
        d[Op.FFTOI_GPR_FP] = self._h_fp_float_to_int

        # Control (149-152)
        d[Op.FSTAT_GPR] = self._h_fp_read_status
        d[Op.FCFG_GPR] = self._h_fp_read_config
        d[Op.FSCFG_GPR] = self._h_fp_write_config
        d[Op.FCLR] = self._h_fp_clear_status

        # Reg-reg (153-157)
        d[Op.FADD_RR] = self._make_fp_arith_rr(fp_add)
        d[Op.FSUB_RR] = self._make_fp_arith_rr(fp_sub)
        d[Op.FMUL_RR] = self._make_fp_arith_rr(fp_mul)
        d[Op.FDIV_RR] = self._make_fp_arith_rr(fp_div)
        d[Op.FCMP_RR] = self._h_fp_cmp_reg_reg

        # FCLASS (158)
        d[Op.FCLASS_GPR_FP] = self._h_fp_classify

        # FMADD (159-160)
        d[Op.FMADD_FP_FP_ADDR] = self._h_fp_madd_direct
        d[Op.FMADD_FP_FP_REGADDR] = self._h_fp_madd_indirect

    # ── Handler factories ──────────────────────────────────────────

    def _fp_apply_arith_mem(
        self, instr: DecodedInstr, arith_fn: Callable[..., tuple[float, FpExceptions]], addr: int
    ) -> None:
        """Apply FP binary op against a memory operand: accumulate exc, write reg back."""
        phys, pos, fmt = self._validate_fpm(instr.operands[0])
        result, exc = arith_fn(
            self._fp_read_reg(pos, fmt, phys), self._fp_read_mem(addr, fmt), fmt, self._fpu.rounding_mode
        )
        self._fpu.accumulate_exceptions(exc)
        self._fp_write_reg(pos, fmt, result, phys)
        self.regs.ip += instr.size

    def _fp_apply_cmp_mem(self, instr: DecodedInstr, addr: int) -> None:
        """FP compare against a memory operand: accumulate exc, update Z and C."""
        phys, pos, fmt = self._validate_fpm(instr.operands[0])
        self._fp_apply_cmp(self._fp_read_reg(pos, fmt, phys), self._fp_read_mem(addr, fmt))
        self.regs.ip += instr.size

    def _make_fp_arith_mem(
        self, arith_fn: Callable[..., tuple[float, FpExceptions]], resolve_addr: Callable[[int], int]
    ) -> Callable[[DecodedInstr], None]:
        return lambda instr: self._fp_apply_arith_mem(instr, arith_fn, resolve_addr(instr.operands[1]))

    def _make_fp_cmp_mem(self, resolve_addr: Callable[[int], int]) -> Callable[[DecodedInstr], None]:
        return lambda instr: self._fp_apply_cmp_mem(instr, resolve_addr(instr.operands[1]))

    def _fp_apply_reg_binary(self, instr: DecodedInstr, arith_fn: Callable[..., tuple[float, FpExceptions]]) -> None:
        """Apply a binary FP op to two FP regs with matching format: accumulate exc, write dst back."""
        dst_phys, dst_pos, dst_fmt, src_phys, src_pos, src_fmt = self._validate_two_fpm_same_fmt(instr)
        result, exc = arith_fn(
            self._fp_read_reg(dst_pos, dst_fmt, dst_phys),
            self._fp_read_reg(src_pos, src_fmt, src_phys),
            dst_fmt,
            self._fpu.rounding_mode,
        )
        self._fpu.accumulate_exceptions(exc)
        self._fp_write_reg(dst_pos, dst_fmt, result, dst_phys)
        self.regs.ip += instr.size

    def _make_fp_arith_rr(
        self,
        arith_fn: Callable[..., tuple[float, FpExceptions]],
    ) -> Callable[[DecodedInstr], None]:
        """Factory for reg-reg FP arithmetic."""
        return lambda instr: self._fp_apply_reg_binary(instr, arith_fn)

    # ── Individual handlers ────────────────────────────────────────

    # -- FMOV (128-131): raw data transfer, no rounding --

    def _fp_load_raw(self, instr: DecodedInstr, addr: int) -> None:
        fpm = instr.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        data = self._fp_read_mem_raw(addr, fmt)
        raw = int.from_bytes(data, "little")
        self._fpu.write_bits(pos, fmt, raw, phys)
        self.regs.ip += instr.size

    def _h_fp_load_direct(self, instr: DecodedInstr) -> None:
        self._fp_load_raw(instr, self._direct_addr(instr.operands[1]))

    def _h_fp_load_indirect(self, instr: DecodedInstr) -> None:
        self._fp_load_raw(instr, self._indirect_addr(instr.operands[1]))

    def _fp_store_raw(self, instr: DecodedInstr, addr: int) -> None:
        fpm = instr.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        raw = self._fpu.read_bits(pos, fmt, phys)
        data = raw.to_bytes(FP_FMT_WIDTH[fmt] // 8, "little")
        self._fp_write_mem_raw(addr, fmt, data)
        self.regs.ip += instr.size

    def _h_fp_store_direct(self, instr: DecodedInstr) -> None:
        self._fp_store_raw(instr, self._direct_addr(instr.operands[1]))

    def _h_fp_store_indirect(self, instr: DecodedInstr) -> None:
        self._fp_store_raw(instr, self._indirect_addr(instr.operands[1]))

    # -- FMOV immediate (161-162): raw bit write, no rounding --

    def _fp_write_imm(self, instr: DecodedInstr, raw_bits: int, valid_fmts: tuple[int, ...]) -> None:
        """Write raw bits to FP register; raise FP_FORMAT fault if fmt not in valid_fmts."""
        phys, pos, fmt = self._validate_fpm(instr.operands[0])
        if fmt not in valid_fmts:
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)
        self._fpu.write_bits(pos, fmt, raw_bits, phys)
        self.regs.ip += instr.size

    def _h_fp_write_imm8(self, instr: DecodedInstr) -> None:
        self._fp_write_imm(instr, instr.operands[1], (FP_FMT_O3, FP_FMT_O2))

    def _h_fp_write_imm16(self, instr: DecodedInstr) -> None:
        self._fp_write_imm(instr, instr.operands[1] | (instr.operands[2] << 8), (FP_FMT_H, FP_FMT_BF))

    # -- FMOV reg-reg (145): [145, dst_fpm_enc, src_fpm_enc] --

    def _h_fp_copy_reg(self, instr: DecodedInstr) -> None:
        dst_phys, dst_pos, dst_fmt, src_phys, src_pos, src_fmt = self._validate_two_fpm_same_fmt(instr)
        raw = self._fpu.read_bits(src_pos, src_fmt, src_phys)
        self._fpu.write_bits(dst_pos, dst_fmt, raw, dst_phys)
        self.regs.ip += instr.size

    # -- FABS (142) / FNEG (143) --

    def _fp_apply_reg_unary(
        self,
        instr: DecodedInstr,
        fn: Callable[..., tuple[float, FpExceptions]],
    ) -> None:
        """Read FP register, apply unary fn(val, fmt, rm), accumulate exc, write back."""
        phys, pos, fmt = self._validate_fpm(instr.operands[0])
        result, exc = fn(self._fp_read_reg(pos, fmt, phys), fmt, self._fpu.rounding_mode)
        self._fpu.accumulate_exceptions(exc)
        self._fp_write_reg(pos, fmt, result, phys)
        self.regs.ip += instr.size

    def _fp_apply_bitwise_unary(
        self,
        instr: DecodedInstr,
        fn: Callable[[int, int], int],
    ) -> None:
        fpm = instr.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        raw = self._fpu.read_bits(pos, fmt, phys)
        result = fn(raw, FP_FMT_WIDTH[fmt])
        self._fpu.write_bits(pos, fmt, result, phys)
        self.regs.ip += instr.size

    def _h_fp_abs(self, instr: DecodedInstr) -> None:
        self._fp_apply_bitwise_unary(instr, fp_abs)

    def _h_fp_neg(self, instr: DecodedInstr) -> None:
        self._fp_apply_bitwise_unary(instr, fp_neg)

    # -- FSQRT (144) --

    def _h_fp_sqrt(self, instr: DecodedInstr) -> None:
        self._fp_apply_reg_unary(instr, fp_sqrt)

    # -- FCVT (146): [146, dst_fpm_enc, src_fpm_enc] --

    def _h_fp_convert_format(self, instr: DecodedInstr) -> None:
        dst_phys, dst_pos, dst_fmt = self._validate_fpm(instr.operands[0])
        src_phys, src_pos, src_fmt = self._validate_fpm(instr.operands[1])
        self._fp_write_reg(dst_pos, dst_fmt, self._fp_read_reg(src_pos, src_fmt, src_phys), dst_phys)
        self.regs.ip += instr.size

    # -- FITOF (147): [147, fpm, gpr] --

    def _h_fp_int_to_float(self, instr: DecodedInstr) -> None:
        phys, pos, fmt = self._validate_fpm(instr.operands[0])
        self._fp_write_reg(pos, fmt, float(self.regs.read(self._decode_gpr(instr.operands[1]))), phys)
        self.regs.ip += instr.size

    # -- FFTOI (148): [148, fpm, gpr] --

    def _fp_float_to_uint8_saturated(self, fp_val: float) -> tuple[int, FpExceptions]:
        """Convert float to uint8 with saturation. Returns (result, exc)."""
        if math.isnan(fp_val):
            return 0, FpExceptions(invalid=True)
        if math.isinf(fp_val):
            return (255 if fp_val > 0 else 0), FpExceptions(invalid=True)
        rounded = _RM_ROUND_FN[self._fpu.rounding_mode](fp_val)
        return max(0, min(255, rounded)), FpExceptions(inexact=rounded != fp_val)

    def _h_fp_float_to_int(self, instr: DecodedInstr) -> None:
        phys, pos, fmt = self._validate_fpm(instr.operands[0])
        gpr = self._decode_gpr(instr.operands[1])
        result, exc = self._fp_float_to_uint8_saturated(self._fp_read_reg(pos, fmt, phys))
        self._fpu.accumulate_exceptions(exc)
        self.regs.write(gpr, result)
        self.regs.ip += instr.size

    # -- FSTAT (149): [149, gpr] --

    def _fp_store_to_gpr(self, instr: DecodedInstr, value: int) -> None:
        """Write value to GPR encoded in operands[0], then advance IP."""
        self.regs.write(self._decode_gpr(instr.operands[0]), value)
        self.regs.ip += instr.size

    def _h_fp_read_status(self, instr: DecodedInstr) -> None:
        self._fp_store_to_gpr(instr, self._fpu.fpsr)

    # -- FCFG (150): [150, gpr] --

    def _h_fp_read_config(self, instr: DecodedInstr) -> None:
        self._fp_store_to_gpr(instr, self._fpu.fpcr)

    # -- FSCFG (151): [151, gpr] --

    def _h_fp_write_config(self, instr: DecodedInstr) -> None:
        self._fpu.fpcr = self.regs.read(self._decode_gpr(instr.operands[0])) & 0x03
        self.regs.ip += instr.size

    # -- FCLR (152): [152] --

    def _h_fp_clear_status(self, instr: DecodedInstr) -> None:
        self._fpu.fpsr = 0
        self.regs.ip += instr.size

    # -- FCMP_RR (157): [157, dst_fpm_enc, src_fpm_enc] --

    def _h_fp_cmp_reg_reg(self, instr: DecodedInstr) -> None:
        dst_phys, dst_pos, dst_fmt, src_phys, src_pos, src_fmt = self._validate_two_fpm_same_fmt(instr)
        self._fp_apply_cmp(self._fp_read_reg(dst_pos, dst_fmt, dst_phys), self._fp_read_reg(src_pos, src_fmt, src_phys))
        self.regs.ip += instr.size

    # -- FCLASS (158): [158, fpm, gpr] --

    def _h_fp_classify(self, instr: DecodedInstr) -> None:
        phys, pos, fmt = self._validate_fpm(instr.operands[0])
        gpr = self._decode_gpr(instr.operands[1])
        val, raw = self._fp_read_reg_and_raw(pos, fmt, phys)
        self.regs.write(gpr, fp_classify(val, raw, FP_FMT_WIDTH[fmt], fmt))
        self.regs.ip += instr.size

    # -- FMADD (159-160): dst = src * mem + dst (unfused: two roundings) --

    def _h_fp_madd_direct(self, instr: DecodedInstr) -> None:
        self._fp_do_madd(instr, self._direct_addr(instr.operands[2]))

    def _h_fp_madd_indirect(self, instr: DecodedInstr) -> None:
        self._fp_do_madd(instr, self._indirect_addr(instr.operands[2]))

    def _fp_do_madd(self, instr: DecodedInstr, addr: int) -> None:
        """FMADD: dst = src * mem + dst (two roundings)."""
        dst_phys, dst_pos, dst_fmt, src_phys, src_pos, src_fmt = self._validate_two_fpm_same_fmt(instr)
        rm = self._fpu.rounding_mode
        mul_result, mul_exc = fp_mul(
            self._fp_read_reg(src_pos, src_fmt, src_phys), self._fp_read_mem(addr, dst_fmt), dst_fmt, rm
        )
        result, add_exc = fp_add(mul_result, self._fp_read_reg(dst_pos, dst_fmt, dst_phys), dst_fmt, rm)
        self._fpu.accumulate_exceptions(self._fp_merge_exc(mul_exc, add_exc))
        self._fp_write_reg(dst_pos, dst_fmt, result, dst_phys)
        self.regs.ip += instr.size
