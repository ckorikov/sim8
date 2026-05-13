"""Matrix Unit state: registers, command queue, and command record."""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from .memory import MEM_SIZE

__all__ = ["MuRegisters", "MuCommand", "MuQueue", "MU_QUEUE_DEPTH"]

MU_QUEUE_DEPTH = 4


@dataclass(slots=True)
class MuCommand:
    """A fully-resolved MMUL/MMAD command (no register references)."""

    op: int
    fmt: int
    a_col: bool
    b_col: bool
    c_col: bool
    accumulate: bool
    a_addr: int
    b_addr: int
    c_addr: int
    m: int  # rows of A and C
    n: int  # cols of B and C
    k: int  # inner dim


class MuRegisters:
    """MU register file: MA, MB, MC (pointers), MM, MN, MK (dims), MFPSR (flags)."""

    __slots__ = ("ma", "mb", "mc", "mm", "mn", "mk", "mfpsr")

    def __init__(self) -> None:
        self.ma: int = 0
        self.mb: int = 0
        self.mc: int = 0
        self.mm: int = 0
        self.mn: int = 0
        self.mk: int = 0
        self.mfpsr: int = 0

    _PTR_ATTRS = ("ma", "mb", "mc")
    _REG_ATTRS = ("ma", "mb", "mc", "mm", "mn", "mk")

    def read_ptr(self, code: int) -> int:
        """Read pointer register by code (0=MA, 1=MB, 2=MC)."""
        if code >= len(self._PTR_ATTRS):
            raise ValueError(f"Invalid MU pointer code: {code}")
        return getattr(self, self._PTR_ATTRS[code])

    def write_reg(self, code: int, val: int) -> None:
        """Write MU register by code (0=MA..5=MK)."""
        if code >= len(self._REG_ATTRS):
            raise ValueError(f"Invalid MU register code: {code}")
        setattr(self, self._REG_ATTRS[code], val & 0xFFFF)

    def inc_ptr(self, code: int, amount: int) -> None:
        """Increment pointer register by amount (mod 64K)."""
        cur = self.read_ptr(code)
        self.write_reg(code, (cur + amount) % MEM_SIZE)

    def reset(self) -> None:
        """Reset all MU registers to zero."""
        self.ma = self.mb = self.mc = 0
        self.mm = self.mn = self.mk = 0
        self.mfpsr = 0

    def __repr__(self) -> str:
        return (
            f"MU(MA=0x{self.ma:04X} MB=0x{self.mb:04X} MC=0x{self.mc:04X} "
            f"MM={self.mm} MN={self.mn} MK={self.mk} MFPSR=0x{self.mfpsr:02X})"
        )


class MuQueue:
    """Fixed-depth FIFO command queue for MU."""

    __slots__ = ("_q", "_fault")

    def __init__(self) -> None:
        self._q: deque[MuCommand] = deque(maxlen=MU_QUEUE_DEPTH)
        self._fault: int = 0

    @property
    def is_empty(self) -> bool:
        return len(self._q) == 0

    @property
    def is_full(self) -> bool:
        return len(self._q) >= MU_QUEUE_DEPTH

    @property
    def fault(self) -> int:
        return self._fault

    @fault.setter
    def fault(self, code: int) -> None:
        self._fault = code

    def peek(self) -> MuCommand:
        return self._q[0]

    def enqueue(self, cmd: MuCommand) -> None:
        if self.is_full:
            raise RuntimeError("MU queue full")
        self._q.append(cmd)

    def dequeue(self) -> MuCommand:
        return self._q.popleft()

    def flush(self) -> None:
        self._q.clear()

    def reset(self) -> None:
        self._q.clear()
        self._fault = 0

    def __len__(self) -> int:
        return len(self._q)
