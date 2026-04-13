"""Instruction decoder: fetch opcode + operands from memory."""

from dataclasses import dataclass

from pysim8.isa import BY_CODE, BY_CODE_FP, BY_CODE_VU, VU_ASYNC_OPS, Op, vu_instr_size

from .errors import CpuFault, ErrorCode
from .memory import PAGE_SIZE, Memory

__all__ = ["DecodedInstr", "Decoder"]


@dataclass(slots=True, frozen=True)
class DecodedInstr:
    """A decoded instruction: opcode enum, size, and raw operand bytes."""

    op: Op
    size: int
    operands: tuple[int, ...]


class Decoder:
    """Stateless instruction decoder."""

    @staticmethod
    def fetch(mem: Memory, ip: int, arch: int = 1) -> DecodedInstr:
        """Fetch and decode one instruction at the given IP.

        Raises CpuFault for invalid opcode or page boundary violation.
        """
        opcode = mem[ip]
        instr_def = BY_CODE.get(opcode)
        if instr_def is None and arch >= 2:
            instr_def = BY_CODE_FP.get(opcode)
        if instr_def is None and arch >= 3:
            instr_def = BY_CODE_VU.get(opcode)
        if instr_def is None:
            raise CpuFault(ErrorCode.INVALID_OPCODE, ip)

        # VU async instructions have variable size (depends on VFM mode/fmt)
        if opcode in VU_ASYNC_OPS:
            vfm_enc = mem[ip + 1] if ip + 1 < PAGE_SIZE else 0
            size = vu_instr_size(opcode, vfm_enc)
        else:
            size = instr_def.size
        if ip + size > PAGE_SIZE:
            raise CpuFault(ErrorCode.PAGE_BOUNDARY, ip)

        operands = tuple(mem[ip + k] for k in range(1, size))
        return DecodedInstr(op=instr_def.op, size=size, operands=operands)
