"""Fault exception and error codes for the CPU simulator."""

from enum import IntEnum

__all__ = ["ErrorCode", "CpuFault"]


class ErrorCode(IntEnum):
    """CPU error codes (from spec/errors.md)."""

    DIV_ZERO = 1
    STACK_OVERFLOW = 2
    STACK_UNDERFLOW = 3
    INVALID_REG = 4
    PAGE_BOUNDARY = 5
    INVALID_OPCODE = 6
    FP_FORMAT = 12


class CpuFault(Exception):
    """Raised when the CPU encounters a fault condition."""

    __slots__ = ("code", "ip")

    def __init__(self, code: ErrorCode, ip: int = 0) -> None:
        self.code = code
        self.ip = ip
        super().__init__(f"FAULT({code.name}) at IP={ip}")
