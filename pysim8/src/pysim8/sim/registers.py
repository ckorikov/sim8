"""Register file, flags, and CPU state enum."""

from enum import Enum

from .memory import SP_INIT

__all__ = ["CpuState", "Flags", "RegisterFile"]


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


class RegisterFile:
    """CPU register file: A(0), B(1), C(2), D(3), SP(4), DP(5) + IP."""

    __slots__ = ("_regs", "ip", "flags")

    def __init__(self) -> None:
        self._regs: list[int] = [0, 0, 0, 0, SP_INIT, 0]
        self.ip: int = 0
        self.flags: Flags = Flags()

    def read(self, code: int) -> int:
        """Read register by code. Caller must validate code is in range."""
        return self._regs[code]

    def write(self, code: int, val: int) -> None:
        """Write register by code. Caller must validate code and mask val."""
        self._regs[code] = val

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

    def reset(self) -> None:
        self._regs[:] = [0, 0, 0, 0, SP_INIT, 0]
        self.ip = 0
        self.flags.reset()

    def __repr__(self) -> str:
        return (
            f"Regs(A={self.a} B={self.b} C={self.c} D={self.d} "
            f"SP={self.sp} DP={self.dp} IP={self.ip} {self.flags!r})"
        )
