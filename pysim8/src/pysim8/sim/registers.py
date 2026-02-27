"""Register file, flags, and CPU state enum."""

from __future__ import annotations

from enum import Enum

from .memory import SP_INIT

__all__ = ["CpuState", "Flags", "FpuRegisters", "RegisterFile"]


class CpuState(Enum):
    """CPU execution states."""

    IDLE = "IDLE"
    RUNNING = "RUNNING"
    HALTED = "HALTED"
    FAULT = "FAULT"


class Flags:
    """CPU flags: Z (zero), C (carry), F (fault)."""

    __slots__ = ("z", "c", "f")

    def __init__(self) -> None:
        self.z: bool = False
        self.c: bool = False
        self.f: bool = False

    def reset(self) -> None:
        self.z = False
        self.c = False
        self.f = False

    def __repr__(self) -> str:
        parts = []
        if self.z:
            parts.append("Z")
        if self.c:
            parts.append("C")
        if self.f:
            parts.append("F")
        return "Flags(" + " ".join(parts) + ")" if parts else "Flags()"


class FpuRegisters:
    """FPU register state: one 32-bit physical register + FPCR + FPSR."""

    __slots__ = ("_fp32", "fpcr", "fpsr")

    def __init__(self) -> None:
        self._fp32: int = 0  # 32-bit raw storage
        self.fpcr: int = 0   # bits[1:0] = rounding mode
        self.fpsr: int = 0   # sticky exception flags

    @property
    def rounding_mode(self) -> int:
        """Return current rounding mode from FPCR bits [1:0]."""
        return self.fpcr & 0x03

    def read_bits(self, pos: int, fmt: int) -> int:
        """Read raw bits from sub-register at (pos, fmt).

        Returns the integer value of the bits slice.
        Uses FP_FMT_WIDTH to determine width.
        """
        from pysim8.isa import FP_FMT_WIDTH

        width = FP_FMT_WIDTH[fmt]
        bit_offset = pos * width
        mask = (1 << width) - 1
        return (self._fp32 >> bit_offset) & mask

    def write_bits(self, pos: int, fmt: int, value: int) -> None:
        """Write raw bits to sub-register at (pos, fmt)."""
        from pysim8.isa import FP_FMT_WIDTH

        width = FP_FMT_WIDTH[fmt]
        bit_offset = pos * width
        mask = (1 << width) - 1
        self._fp32 = (
            (self._fp32 & ~(mask << bit_offset))
            | ((value & mask) << bit_offset)
        )

    def accumulate_exceptions(self, exc: object) -> None:
        """OR exception flags into FPSR (sticky)."""
        if exc.invalid:  # type: ignore[union-attr]
            self.fpsr |= 0x01
        if exc.div_zero:  # type: ignore[union-attr]
            self.fpsr |= 0x02
        if exc.overflow:  # type: ignore[union-attr]
            self.fpsr |= 0x04
        if exc.underflow:  # type: ignore[union-attr]
            self.fpsr |= 0x08
        if exc.inexact:  # type: ignore[union-attr]
            self.fpsr |= 0x10

    def reset(self) -> None:
        """Reset all FPU state to zero."""
        self._fp32 = 0
        self.fpcr = 0
        self.fpsr = 0

    def __repr__(self) -> str:
        return (
            f"FPU(fp32=0x{self._fp32:08X}"
            f" FPCR={self.fpcr:02X} FPSR={self.fpsr:02X})"
        )


class RegisterFile:
    """CPU register file: A(0), B(1), C(2), D(3), SP(4), DP(5) + IP."""

    __slots__ = ("_regs", "ip", "flags", "fpu")

    def __init__(self, arch: int = 1) -> None:
        self._regs: list[int] = [0, 0, 0, 0, SP_INIT, 0]
        self.ip: int = 0
        self.flags: Flags = Flags()
        self.fpu: FpuRegisters | None = (
            FpuRegisters() if arch >= 2 else None
        )

    def read(self, code: int) -> int:
        """Read register by code. Caller must validate code is in range."""
        return self._regs[code]

    def write(self, code: int, val: int) -> None:
        """Write register by code. Caller must validate code."""
        self._regs[code] = val & 0xFF

    @property
    def a(self) -> int:
        return self._regs[0]

    @a.setter
    def a(self, val: int) -> None:
        self._regs[0] = val

    @property
    def b(self) -> int:
        return self._regs[1]

    @b.setter
    def b(self, val: int) -> None:
        self._regs[1] = val

    @property
    def c(self) -> int:
        return self._regs[2]

    @c.setter
    def c(self, val: int) -> None:
        self._regs[2] = val

    @property
    def d(self) -> int:
        return self._regs[3]

    @d.setter
    def d(self, val: int) -> None:
        self._regs[3] = val

    @property
    def sp(self) -> int:
        return self._regs[4]

    @sp.setter
    def sp(self, val: int) -> None:
        self._regs[4] = val

    @property
    def dp(self) -> int:
        return self._regs[5]

    @dp.setter
    def dp(self, val: int) -> None:
        self._regs[5] = val

    def reset(self, arch: int = 1) -> None:
        """Reset register file to initial state."""
        self._regs[:] = [0, 0, 0, 0, SP_INIT, 0]
        self.ip = 0
        self.flags.reset()
        if arch >= 2:
            if self.fpu is None:
                self.fpu = FpuRegisters()
            else:
                self.fpu.reset()
        else:
            self.fpu = None

    def __repr__(self) -> str:
        return (
            f"Regs(A={self.a} B={self.b} C={self.c} D={self.d} "
            f"SP={self.sp} DP={self.dp} IP={self.ip} {self.flags!r})"
        )
