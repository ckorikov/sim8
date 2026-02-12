"""Instruction decoder: fetch opcode + operands from memory."""

from dataclasses import dataclass

from pysim8.isa import BY_CODE, Op

from .errors import CpuFault, ErrorCode
from .memory import PAGE_SIZE, Memory

__all__ = ["DecodedInsn", "Decoder"]


@dataclass(slots=True, frozen=True)
class DecodedInsn:
    """A decoded instruction: opcode enum, size, and raw operand bytes."""

    op: Op
    size: int
    operands: tuple[int, ...]


class Decoder:
    """Stateless instruction decoder."""

    @staticmethod
    def fetch(mem: Memory, ip: int) -> DecodedInsn:
        """Fetch and decode one instruction at the given IP.

        Raises CpuFault for invalid opcode or page boundary violation.
        """
        opcode = mem[ip]
        defn = BY_CODE.get(opcode)
        if defn is None:
            raise CpuFault(ErrorCode.INVALID_OPCODE, ip)

        size = defn.size
        if ip + size > PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, ip)

        operands = tuple(mem[ip + k] for k in range(1, size))
        return DecodedInsn(op=defn.op, size=size, operands=operands)
