"""FP instruction handlers for the CPU simulator."""

from __future__ import annotations

import math
from collections.abc import Callable
from typing import TYPE_CHECKING

from pysim8.isa import (
    Op,
    FP_FMT_H,
    FP_FMT_BF,
    FP_FMT_O3,
    FP_FMT_O2,
    FP_FMT_WIDTH,
    decode_fpm,
    validate_fpm,
)
from pysim8.fp_formats import (
    FpExceptions,
    bytes_to_float,
    float_to_bytes,
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

from .decoder import DecodedInsn
from .errors import CpuFault, ErrorCode
from .memory import Memory

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

    def _direct_addr(self, offset: int) -> int: ...
    def _indirect_addr(self, encoded: int) -> int: ...
    def _decode_gpr(self, code: int) -> int: ...

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

    # ── Memory helpers ─────────────────────────────────────────────

    def _fp_read_mem_raw(self, addr: int, fmt: int) -> bytes:
        """Read raw bytes from memory for an FP value."""
        width = FP_FMT_WIDTH[fmt]
        nbytes = width // 8
        page_offset = addr % Memory.PAGE_SIZE
        if page_offset + nbytes > Memory.PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)
        return bytes(self.mem[addr + i] for i in range(nbytes))

    def _fp_read_mem(self, addr: int, fmt: int) -> float:
        """Read FP value from memory (little-endian)."""
        data = self._fp_read_mem_raw(addr, fmt)
        return bytes_to_float(data, fmt)

    def _fp_write_mem_raw(
        self, addr: int, fmt: int, data: bytes,
    ) -> None:
        """Write raw bytes to memory."""
        width = FP_FMT_WIDTH[fmt]
        nbytes = width // 8
        page_offset = addr % Memory.PAGE_SIZE
        if page_offset + nbytes > Memory.PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, self.regs.ip)
        for i, b in enumerate(data):
            self.mem[addr + i] = b

    # ── Register helpers ───────────────────────────────────────────

    def _fp_read_reg(
        self, pos: int, fmt: int, phys: int = 0,
    ) -> float:
        """Read FP register as float value."""
        raw = self._fpu.read_bits(pos, fmt, phys)
        width = FP_FMT_WIDTH[fmt]
        data = raw.to_bytes(width // 8, "little")
        return bytes_to_float(data, fmt)

    def _fp_write_reg(
        self, pos: int, fmt: int, value: float, phys: int = 0,
    ) -> None:
        """Write float value to FP register (with rounding)."""
        data, exc = float_to_bytes(
            value, fmt, self._fpu.rounding_mode,
        )
        self._fpu.accumulate_exceptions(exc)
        raw = int.from_bytes(data, "little")
        self._fpu.write_bits(pos, fmt, raw, phys)

    # ── Dispatch registration ──────────────────────────────────────

    def _build_fp_dispatch(self) -> None:
        """Register all FP instruction handlers."""
        d = self._dispatch

        # FMOV (128-131, 161-162)
        d[Op.FMOV_FP_ADDR] = self._h_fmov_load_addr
        d[Op.FMOV_FP_REGADDR] = self._h_fmov_load_regaddr
        d[Op.FMOV_ADDR_FP] = self._h_fmov_store_addr
        d[Op.FMOV_REGADDR_FP] = self._h_fmov_store_regaddr
        d[Op.FMOV_FP_IMM8] = self._h_fmov_imm8
        d[Op.FMOV_FP_IMM16] = self._h_fmov_imm16

        # Arithmetic mem variants (132-141)
        d[Op.FADD_FP_ADDR] = self._make_fp_arith_mem(
            fp_add, self._direct_addr,
        )
        d[Op.FADD_FP_REGADDR] = self._make_fp_arith_mem(
            fp_add, self._indirect_addr,
        )
        d[Op.FSUB_FP_ADDR] = self._make_fp_arith_mem(
            fp_sub, self._direct_addr,
        )
        d[Op.FSUB_FP_REGADDR] = self._make_fp_arith_mem(
            fp_sub, self._indirect_addr,
        )
        d[Op.FMUL_FP_ADDR] = self._make_fp_arith_mem(
            fp_mul, self._direct_addr,
        )
        d[Op.FMUL_FP_REGADDR] = self._make_fp_arith_mem(
            fp_mul, self._indirect_addr,
        )
        d[Op.FDIV_FP_ADDR] = self._make_fp_arith_mem(
            fp_div, self._direct_addr,
        )
        d[Op.FDIV_FP_REGADDR] = self._make_fp_arith_mem(
            fp_div, self._indirect_addr,
        )
        d[Op.FCMP_FP_ADDR] = self._make_fp_cmp_mem(
            self._direct_addr,
        )
        d[Op.FCMP_FP_REGADDR] = self._make_fp_cmp_mem(
            self._indirect_addr,
        )

        # Unary (142-144)
        d[Op.FABS_FP] = self._h_fabs
        d[Op.FNEG_FP] = self._h_fneg
        d[Op.FSQRT_FP] = self._h_fsqrt

        # FMOV reg-reg (145)
        d[Op.FMOV_RR] = self._h_fmov_rr

        # FCVT (146)
        d[Op.FCVT_FP_FP] = self._h_fcvt

        # FITOF/FFTOI (147-148)
        d[Op.FITOF_FP_GPR] = self._h_fitof
        d[Op.FFTOI_GPR_FP] = self._h_fftoi

        # Control (149-152)
        d[Op.FSTAT_GPR] = self._h_fstat
        d[Op.FCFG_GPR] = self._h_fcfg
        d[Op.FSCFG_GPR] = self._h_fscfg
        d[Op.FCLR] = self._h_fclr

        # Reg-reg (153-157)
        d[Op.FADD_RR] = self._make_fp_arith_rr(fp_add)
        d[Op.FSUB_RR] = self._make_fp_arith_rr(fp_sub)
        d[Op.FMUL_RR] = self._make_fp_arith_rr(fp_mul)
        d[Op.FDIV_RR] = self._make_fp_arith_rr(fp_div)
        d[Op.FCMP_RR] = self._h_fcmp_rr

        # FCLASS (158)
        d[Op.FCLASS_GPR_FP] = self._h_fclass

        # FMADD (159-160)
        d[Op.FMADD_FP_FP_ADDR] = self._h_fmadd_addr
        d[Op.FMADD_FP_FP_REGADDR] = self._h_fmadd_regaddr

    # ── Handler factories ──────────────────────────────────────────

    def _make_fp_arith_mem(
        self,
        arith_fn: Callable[..., tuple[float, FpExceptions]],
        resolve_addr: Callable[[int], int],
    ) -> Callable[[DecodedInsn], None]:
        """Factory for FP arith with memory operand."""

        def handler(insn: DecodedInsn) -> None:
            fpm = insn.operands[0]
            phys, pos, fmt = self._validate_fpm(fpm)
            addr = resolve_addr(insn.operands[1])

            reg_val = self._fp_read_reg(pos, fmt, phys)
            mem_val = self._fp_read_mem(addr, fmt)

            result, exc = arith_fn(
                reg_val, mem_val, fmt, self._fpu.rounding_mode,
            )
            self._fpu.accumulate_exceptions(exc)
            self._fp_write_reg(pos, fmt, result, phys)
            self.regs.ip += insn.size

        return handler

    def _make_fp_cmp_mem(
        self,
        resolve_addr: Callable[[int], int],
    ) -> Callable[[DecodedInsn], None]:
        """Factory for FCMP with memory operand."""

        def handler(insn: DecodedInsn) -> None:
            fpm = insn.operands[0]
            phys, pos, fmt = self._validate_fpm(fpm)
            addr = resolve_addr(insn.operands[1])

            reg_val = self._fp_read_reg(pos, fmt, phys)
            mem_val = self._fp_read_mem(addr, fmt)

            z, c, exc = fp_cmp(reg_val, mem_val)
            self._fpu.accumulate_exceptions(exc)
            self.regs.flags.z = z
            self.regs.flags.c = c
            self.regs.ip += insn.size

        return handler

    def _make_fp_arith_rr(
        self,
        arith_fn: Callable[..., tuple[float, FpExceptions]],
    ) -> Callable[[DecodedInsn], None]:
        """Factory for reg-reg FP arithmetic."""

        def handler(insn: DecodedInsn) -> None:
            dst_fpm = insn.operands[0]
            src_fpm = insn.operands[1]
            dst_phys, dst_pos, dst_fmt = self._validate_fpm(dst_fpm)
            src_phys, src_pos, src_fmt = self._validate_fpm(src_fpm)

            if dst_fmt != src_fmt:
                raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)

            dst_val = self._fp_read_reg(dst_pos, dst_fmt, dst_phys)
            src_val = self._fp_read_reg(src_pos, src_fmt, src_phys)

            result, exc = arith_fn(
                dst_val, src_val, dst_fmt, self._fpu.rounding_mode,
            )
            self._fpu.accumulate_exceptions(exc)
            self._fp_write_reg(dst_pos, dst_fmt, result, dst_phys)
            self.regs.ip += insn.size

        return handler

    # ── Individual handlers ────────────────────────────────────────

    # -- FMOV (128-131): raw data transfer, no rounding --

    def _fmov_load(self, insn: DecodedInsn, addr: int) -> None:
        fpm = insn.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        data = self._fp_read_mem_raw(addr, fmt)
        raw = int.from_bytes(data, "little")
        self._fpu.write_bits(pos, fmt, raw, phys)
        self.regs.ip += insn.size

    def _h_fmov_load_addr(self, insn: DecodedInsn) -> None:
        self._fmov_load(insn, self._direct_addr(insn.operands[1]))

    def _h_fmov_load_regaddr(self, insn: DecodedInsn) -> None:
        self._fmov_load(insn, self._indirect_addr(insn.operands[1]))

    def _fmov_store(self, insn: DecodedInsn, addr: int) -> None:
        fpm = insn.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        raw = self._fpu.read_bits(pos, fmt, phys)
        data = raw.to_bytes(FP_FMT_WIDTH[fmt] // 8, "little")
        self._fp_write_mem_raw(addr, fmt, data)
        self.regs.ip += insn.size

    def _h_fmov_store_addr(self, insn: DecodedInsn) -> None:
        self._fmov_store(insn, self._direct_addr(insn.operands[1]))

    def _h_fmov_store_regaddr(self, insn: DecodedInsn) -> None:
        self._fmov_store(insn, self._indirect_addr(insn.operands[1]))

    # -- FMOV immediate (161-162): raw bit write, no rounding --

    def _h_fmov_imm8(self, insn: DecodedInsn) -> None:
        fpm = insn.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        if fmt not in (FP_FMT_O3, FP_FMT_O2):
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)
        imm8 = insn.operands[1]
        self._fpu.write_bits(pos, fmt, imm8, phys)
        self.regs.ip += insn.size

    def _h_fmov_imm16(self, insn: DecodedInsn) -> None:
        fpm = insn.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        if fmt not in (FP_FMT_H, FP_FMT_BF):
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)
        imm16 = insn.operands[1] | (insn.operands[2] << 8)
        self._fpu.write_bits(pos, fmt, imm16, phys)
        self.regs.ip += insn.size

    # -- FMOV reg-reg (145): [145, dst_fpm, src_fpm] --

    def _h_fmov_rr(self, insn: DecodedInsn) -> None:
        dst_fpm = insn.operands[0]
        src_fpm = insn.operands[1]
        dst_phys, dst_pos, dst_fmt = self._validate_fpm(dst_fpm)
        src_phys, src_pos, src_fmt = self._validate_fpm(src_fpm)
        if dst_fmt != src_fmt:
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)
        raw = self._fpu.read_bits(src_pos, src_fmt, src_phys)
        self._fpu.write_bits(dst_pos, dst_fmt, raw, dst_phys)
        self.regs.ip += insn.size

    # -- FABS (142) / FNEG (143) --

    def _fp_unary_bitwise(
        self, insn: DecodedInsn,
        fn: Callable[[int, int], int],
    ) -> None:
        fpm = insn.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        raw = self._fpu.read_bits(pos, fmt, phys)
        result = fn(raw, FP_FMT_WIDTH[fmt])
        self._fpu.write_bits(pos, fmt, result, phys)
        self.regs.ip += insn.size

    def _h_fabs(self, insn: DecodedInsn) -> None:
        self._fp_unary_bitwise(insn, fp_abs)

    def _h_fneg(self, insn: DecodedInsn) -> None:
        self._fp_unary_bitwise(insn, fp_neg)

    # -- FSQRT (144) --

    def _h_fsqrt(self, insn: DecodedInsn) -> None:
        fpm = insn.operands[0]
        phys, pos, fmt = self._validate_fpm(fpm)
        val = self._fp_read_reg(pos, fmt, phys)
        result, exc = fp_sqrt(val, fmt, self._fpu.rounding_mode)
        self._fpu.accumulate_exceptions(exc)
        self._fp_write_reg(pos, fmt, result, phys)
        self.regs.ip += insn.size

    # -- FCVT (146): [146, dst_fpm, src_fpm] --

    def _h_fcvt(self, insn: DecodedInsn) -> None:
        dst_fpm = insn.operands[0]
        src_fpm = insn.operands[1]
        dst_phys, dst_pos, dst_fmt = self._validate_fpm(dst_fpm)
        src_phys, src_pos, src_fmt = self._validate_fpm(src_fpm)
        src_val = self._fp_read_reg(src_pos, src_fmt, src_phys)
        self._fp_write_reg(dst_pos, dst_fmt, src_val, dst_phys)
        self.regs.ip += insn.size

    # -- FITOF (147): [147, fpm, gpr] --

    def _h_fitof(self, insn: DecodedInsn) -> None:
        fpm = insn.operands[0]
        gpr_code = insn.operands[1]
        phys, pos, fmt = self._validate_fpm(fpm)
        gpr = self._decode_gpr(gpr_code)
        int_val = self.regs.read(gpr)
        self._fp_write_reg(pos, fmt, float(int_val), phys)
        self.regs.ip += insn.size

    # -- FFTOI (148): [148, fpm, gpr] --

    def _h_fftoi(self, insn: DecodedInsn) -> None:
        fpm = insn.operands[0]
        gpr_code = insn.operands[1]
        phys, pos, fmt = self._validate_fpm(fpm)
        gpr = self._decode_gpr(gpr_code)
        fp_val = self._fp_read_reg(pos, fmt, phys)

        exc_invalid = False
        exc_inexact = False

        if math.isnan(fp_val):
            result = 0
            exc_invalid = True
        elif math.isinf(fp_val):
            result = 255 if fp_val > 0 else 0
            exc_invalid = True
        else:
            rm = self._fpu.rounding_mode
            if rm == 0:  # RNE
                rounded = round(fp_val)
            elif rm == 1:  # RTZ
                rounded = int(fp_val)
            elif rm == 2:  # RDN
                rounded = math.floor(fp_val)
            else:  # RUP
                rounded = math.ceil(fp_val)

            if rounded != fp_val:
                exc_inexact = True

            # Saturate to uint8
            if rounded > 255:
                result = 255
            elif rounded < 0:
                result = 0
            else:
                result = rounded

        self._fpu.accumulate_exceptions(
            FpExceptions(invalid=exc_invalid, inexact=exc_inexact),
        )
        self.regs.write(gpr, result)
        self.regs.ip += insn.size

    # -- FSTAT (149): [149, gpr] --

    def _h_fstat(self, insn: DecodedInsn) -> None:
        gpr = self._decode_gpr(insn.operands[0])
        self.regs.write(gpr, self._fpu.fpsr)
        self.regs.ip += insn.size

    # -- FCFG (150): [150, gpr] --

    def _h_fcfg(self, insn: DecodedInsn) -> None:
        gpr = self._decode_gpr(insn.operands[0])
        self.regs.write(gpr, self._fpu.fpcr)
        self.regs.ip += insn.size

    # -- FSCFG (151): [151, gpr] --

    def _h_fscfg(self, insn: DecodedInsn) -> None:
        gpr = self._decode_gpr(insn.operands[0])
        val = self.regs.read(gpr)
        self._fpu.fpcr = val & 0x03  # mask reserved bits
        self.regs.ip += insn.size

    # -- FCLR (152): [152] --

    def _h_fclr(self, insn: DecodedInsn) -> None:
        self._fpu.fpsr = 0
        self.regs.ip += insn.size

    # -- FCMP_RR (157): [157, dst_fpm, src_fpm] --

    def _h_fcmp_rr(self, insn: DecodedInsn) -> None:
        dst_fpm = insn.operands[0]
        src_fpm = insn.operands[1]
        dst_phys, dst_pos, dst_fmt = self._validate_fpm(dst_fpm)
        src_phys, src_pos, src_fmt = self._validate_fpm(src_fpm)
        if dst_fmt != src_fmt:
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)

        dst_val = self._fp_read_reg(dst_pos, dst_fmt, dst_phys)
        src_val = self._fp_read_reg(src_pos, src_fmt, src_phys)

        z, c, exc = fp_cmp(dst_val, src_val)
        self._fpu.accumulate_exceptions(exc)
        self.regs.flags.z = z
        self.regs.flags.c = c
        self.regs.ip += insn.size

    # -- FCLASS (158): [158, fpm, gpr] --

    def _h_fclass(self, insn: DecodedInsn) -> None:
        fpm = insn.operands[0]
        gpr_code = insn.operands[1]
        phys, pos, fmt = self._validate_fpm(fpm)
        gpr = self._decode_gpr(gpr_code)

        raw = self._fpu.read_bits(pos, fmt, phys)
        width = FP_FMT_WIDTH[fmt]
        data = raw.to_bytes(width // 8, "little")
        val = bytes_to_float(data, fmt)

        mask = fp_classify(val, raw, width, fmt)
        self.regs.write(gpr, mask)
        self.regs.ip += insn.size

    # -- FMADD (159-160): dst = src * mem + dst (unfused: two roundings) --

    def _h_fmadd_addr(self, insn: DecodedInsn) -> None:
        self._do_fmadd(insn, self._direct_addr(insn.operands[2]))

    def _h_fmadd_regaddr(self, insn: DecodedInsn) -> None:
        self._do_fmadd(insn, self._indirect_addr(insn.operands[2]))

    def _do_fmadd(self, insn: DecodedInsn, addr: int) -> None:
        """FMADD: dst = src * mem + dst."""
        dst_fpm = insn.operands[0]
        src_fpm = insn.operands[1]
        dst_phys, dst_pos, dst_fmt = self._validate_fpm(dst_fpm)
        src_phys, src_pos, src_fmt = self._validate_fpm(src_fpm)

        if dst_fmt != src_fmt:
            raise CpuFault(ErrorCode.FP_FORMAT, self.regs.ip)

        src_val = self._fp_read_reg(src_pos, src_fmt, src_phys)
        mem_val = self._fp_read_mem(addr, dst_fmt)
        dst_val = self._fp_read_reg(dst_pos, dst_fmt, dst_phys)

        mul_result, mul_exc = fp_mul(
            src_val, mem_val, dst_fmt, self._fpu.rounding_mode,
        )
        result, add_exc = fp_add(
            mul_result, dst_val, dst_fmt, self._fpu.rounding_mode,
        )

        combined = FpExceptions(
            invalid=mul_exc.invalid or add_exc.invalid,
            div_zero=mul_exc.div_zero or add_exc.div_zero,
            overflow=mul_exc.overflow or add_exc.overflow,
            underflow=mul_exc.underflow or add_exc.underflow,
            inexact=mul_exc.inexact or add_exc.inexact,
        )
        self._fpu.accumulate_exceptions(combined)
        self._fp_write_reg(dst_pos, dst_fmt, result, dst_phys)
        self.regs.ip += insn.size
