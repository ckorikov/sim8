"""Vector Unit state: registers, command queue, and command record."""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from .memory import MEM_SIZE

__all__ = ["VuRegisters", "VuCommand", "VuQueue"]

VU_QUEUE_DEPTH = 4


@dataclass(slots=True)
class VuCommand:
    """A fully-resolved VU command (no register references)."""

    op: int
    fmt: int
    mode: int
    cond: int
    dst_addr: int
    s1_addr: int
    s2_addr: int
    mask_addr: int
    vl: int
    imm: int
    progress: int = 0  # elements processed so far (windowed execution)
    compact_idx: int = 0  # packed index for VGATHER/VSCATTER


class VuRegisters:
    """VU register file: VA, VB, VC, VM, VL (16-bit), VFPSR (8-bit)."""

    __slots__ = ("va", "vb", "vc", "vm", "vl", "vfpsr")

    def __init__(self) -> None:
        self.va: int = 0
        self.vb: int = 0
        self.vc: int = 0
        self.vm: int = 0
        self.vl: int = 0
        self.vfpsr: int = 0

    _PTR_ATTRS = ("va", "vb", "vc", "vm")
    _REG_ATTRS = ("va", "vb", "vc", "vm", "vl")

    def read_ptr(self, code: int) -> int:
        """Read pointer register by code (0=VA, 1=VB, 2=VC, 3=VM)."""
        if code >= len(self._PTR_ATTRS):
            raise ValueError(f"Invalid VU pointer code: {code}")
        return getattr(self, self._PTR_ATTRS[code])

    def write_reg(self, code: int, val: int) -> None:
        """Write VU register by code (0=VA, 1=VB, 2=VC, 3=VM, 4=VL)."""
        if code >= len(self._REG_ATTRS):
            raise ValueError(f"Invalid VU register code: {code}")
        setattr(self, self._REG_ATTRS[code], val & 0xFFFF)

    def inc_ptr(self, code: int, amount: int) -> None:
        """Increment pointer register by amount (mod 64K)."""
        cur = self.read_ptr(code)
        self.write_reg(code, (cur + amount) % MEM_SIZE)

    def reset(self) -> None:
        """Reset all VU registers to zero."""
        self.va = self.vb = self.vc = self.vm = self.vl = self.vfpsr = 0

    def __repr__(self) -> str:
        return (
            f"VU(VA=0x{self.va:04X} VB=0x{self.vb:04X} VC=0x{self.vc:04X} "
            f"VM=0x{self.vm:04X} VL={self.vl} VFPSR=0x{self.vfpsr:02X})"
        )


class VuQueue:
    """Fixed-depth FIFO command queue."""

    __slots__ = ("_q", "_fault")

    def __init__(self) -> None:
        self._q: deque[VuCommand] = deque(maxlen=VU_QUEUE_DEPTH)
        self._fault: int = 0

    @property
    def is_empty(self) -> bool:
        return len(self._q) == 0

    @property
    def is_full(self) -> bool:
        return len(self._q) >= VU_QUEUE_DEPTH

    @property
    def fault(self) -> int:
        return self._fault

    @fault.setter
    def fault(self, code: int) -> None:
        self._fault = code

    def peek(self) -> VuCommand:
        """Return the front command without removing it."""
        return self._q[0]

    def enqueue(self, cmd: VuCommand) -> None:
        """Push a command. Raises if full (caller should stall)."""
        if self.is_full:
            raise RuntimeError("VU queue full")
        self._q.append(cmd)

    def dequeue(self) -> VuCommand:
        """Pop the next command."""
        return self._q.popleft()

    def flush(self) -> None:
        """Discard all pending commands."""
        self._q.clear()

    def reset(self) -> None:
        """Reset queue and fault state."""
        self._q.clear()
        self._fault = 0

    def __len__(self) -> int:
        return len(self._q)
