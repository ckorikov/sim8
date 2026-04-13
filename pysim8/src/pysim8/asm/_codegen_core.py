"""Shared operand-matching and encoding helpers used by all codegen modules."""

from __future__ import annotations

from collections.abc import Mapping

from pysim8.asm.parser import (
    AsmError,
    OpAddr,
    OpAddrLabel,
    OpConst,
    Operand,
    OpFpImm,
    OpFpReg,
    OpLabel,
    OpPageLabel,
    OpReg,
    OpRegAddr,
)
from pysim8.isa import (
    ARITH_CODES,
    BY_MNEMONIC,
    GPR_CODES,
    STACK_CODES,
    InstrDef,
    OpType,
    encode_regaddr,
)


class AssemblerError(AsmError):
    """Assembler error (encoding/resolution phase)."""


def _operand_matches(op: Operand, ot: OpType) -> bool:
    """Check if a parsed operand matches an ISA operand type."""
    match ot:
        case OpType.REG:
            return isinstance(op, OpReg)
        case OpType.REG_ARITH:
            return isinstance(op, OpReg) and op.code in ARITH_CODES
        case OpType.REG_GPR:
            return isinstance(op, OpReg) and op.code in GPR_CODES
        case OpType.REG_STACK:
            return isinstance(op, OpReg) and op.code in STACK_CODES
        case OpType.IMM:
            return isinstance(op, (OpConst, OpLabel, OpPageLabel))
        case OpType.MEM:
            return isinstance(op, (OpAddr, OpAddrLabel))
        case OpType.REGADDR:
            return isinstance(op, OpRegAddr)
        case OpType.FP_REG:
            return isinstance(op, OpFpReg)
        case OpType.FP_IMM8 | OpType.FP_IMM16:
            return isinstance(op, OpFpImm)
    return False


def _encode_operand(op: Operand) -> int:
    """Encode one operand into a single byte."""
    match op:
        case OpReg(code=c):
            return c
        case OpConst(value=v):
            return v
        case OpAddr(value=v):
            return v
        case OpRegAddr() as ra:
            return encode_regaddr(ra.reg_code, ra.offset)
        case OpLabel():
            return 0  # placeholder for pass 2
        case OpAddrLabel():
            return 0  # placeholder for pass 2
        case OpPageLabel():
            return 0  # placeholder for pass 2
    raise AssertionError(f"unexpected operand: {op!r}")


def _find_instr(
    mnemonic: str,
    operands: list[Operand],
    line: int,
    table: Mapping[str, tuple[InstrDef, ...]] | None = None,
) -> InstrDef:
    """Find matching InstrDef by mnemonic and operands."""
    if table is None:
        table = BY_MNEMONIC
    candidates = table.get(mnemonic)
    if candidates is None:
        raise AssemblerError(f"Invalid instruction: {mnemonic}", line)

    for instr in candidates:
        if len(instr.format) != len(operands):
            continue
        if all(_operand_matches(op, ot) for op, ot in zip(operands, instr.format)):
            return instr

    max_arity = max(len(i.format) for i in candidates)
    if len(operands) > max_arity:
        raise AssemblerError(f"{mnemonic}: too many arguments", line)
    raise AssemblerError(f"{mnemonic} does not support this operand(s)", line)


def _lookup_suffix(suffix: str, table: dict[str, int], error_desc: str, line: int) -> int:
    """Upper-case suffix → table lookup. Raises AssemblerError if not found."""
    upper = suffix.upper()
    if upper not in table:
        raise AssemblerError(f"{error_desc}: .{suffix}", line)
    return table[upper]
