"""Two-pass assembler: parse → encode → resolve labels."""

from __future__ import annotations

from dataclasses import dataclass, field

from pysim8.isa import (
    Ot, Reg, InsnDef, BY_MNEMONIC, GPR_CODES, STACK_CODES, encode_regaddr,
)
from pysim8.asm.parser import (
    AsmError,
    OpReg,
    OpConst,
    OpAddr,
    OpRegAddr,
    OpString,
    OpLabel,
    Operand,
    ParseError,
    parse_lines,
)

__all__ = ["assemble", "AssemblerError", "AssembleResult"]


class AssemblerError(AsmError):
    """Assembler error (encoding/resolution phase)."""


@dataclass(slots=True)
class AssembleResult:
    """Result of assembling source code."""

    code: list[int] = field(default_factory=list)
    labels: dict[str, int] = field(default_factory=dict)
    mapping: dict[int, int] = field(default_factory=dict)


# ── Operand matching and encoding ──────────────────────────────────


def _operand_matches(op: Operand, ot: Ot) -> bool:
    """Check if a parsed operand matches an ISA operand type."""
    match ot:
        case Ot.REG:
            return isinstance(op, OpReg)
        case Ot.REG_STACK:
            return isinstance(op, OpReg) and op.code in STACK_CODES
        case Ot.REG_GPR:
            return isinstance(op, OpReg) and op.code in GPR_CODES
        case Ot.IMM:
            return isinstance(op, (OpConst, OpLabel))
        case Ot.MEM:
            return isinstance(op, OpAddr)
        case Ot.REGADDR:
            return isinstance(op, OpRegAddr)
    return False  # pragma: no cover


def _encode_regaddr(ra: OpRegAddr) -> int:
    return encode_regaddr(ra.reg_code, ra.offset)


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
            return _encode_regaddr(ra)
        case OpLabel():
            return 0  # placeholder for pass 2
    raise AssertionError(f"unexpected operand: {op!r}")  # pragma: no cover


def _find_insn(
    mnemonic: str, operands: list[Operand], line: int
) -> InsnDef:
    """Find matching InsnDef by mnemonic and operands."""
    candidates = BY_MNEMONIC.get(mnemonic)
    if candidates is None:
        raise AssemblerError(f"Invalid instruction: {mnemonic}", line)

    for insn in candidates:
        if len(insn.sig) != len(operands):
            continue
        if all(
            _operand_matches(op, ot)
            for op, ot in zip(operands, insn.sig)
        ):
            return insn

    # No match — pick appropriate error
    max_arity = max(len(i.sig) for i in candidates)
    if len(operands) > max_arity:
        raise AssemblerError(
            f"{mnemonic}: too many arguments", line
        )
    raise AssemblerError(
        f"{mnemonic} does not support this operand(s)", line
    )


# ── DB encoding ────────────────────────────────────────────────────


def _encode_db(operands: list[Operand], line: int) -> list[int]:
    """Encode DB pseudo-instruction."""
    result: list[int] = []
    for op in operands:
        match op:
            case OpConst(value=v):
                result.append(v)
            case OpString(text=s):
                result.extend(ord(c) for c in s)
            case _:
                raise AssemblerError(
                    "DB does not support this operand", line
                )
    return result


# ── Instruction encoding ──────────────────────────────────────────


def _encode_instruction(
    mnemonic: str,
    operands: list[Operand],
    line: int,
) -> list[int]:
    """Encode one instruction into bytes."""
    if mnemonic == "DB":
        return _encode_db(operands, line)
    insn = _find_insn(mnemonic, operands, line)
    return [insn.op] + [_encode_operand(op) for op in operands]


# ── Two-pass assembly ───────────────────────────────────────────────


def assemble(source: str) -> AssembleResult:
    """Assemble source code into machine code.

    Returns AssembleResult with:
        code — machine code bytes
        labels — label name → address
        mapping — code position → source line
    """
    try:
        parsed = parse_lines(source)
    except ParseError as e:
        raise AssemblerError(e.message, e.line) from e

    # ── Pass 1: generate code, collect labels ───────
    code: list[int] = []
    labels: dict[str, int] = {}
    mapping: dict[int, int] = {}
    label_patches: list[tuple[int, str, int]] = []

    for pline in parsed:
        pos = len(code)

        if pline.label is not None:
            labels[pline.label] = pos

        if pline.mnemonic is None:
            continue

        operands = pline.operands if pline.operands is not None else []

        encoded = _encode_instruction(
            pline.mnemonic, operands, pline.line_no
        )

        if pline.mnemonic != "DB":
            mapping[pos] = pline.line_no

        if operands:
            for i, op in enumerate(operands):
                if isinstance(op, OpLabel):
                    label_patches.append(
                        (pos + 1 + i, op.name, pline.line_no)
                    )

        code.extend(encoded)

    # ── Pass 2: resolve labels ──────────────────────
    for patch_pos, label_name, line_no in label_patches:
        if label_name not in labels:
            raise AssemblerError(
                f"Undefined label: {label_name}", line_no
            )
        addr = labels[label_name]
        if addr < 0 or addr > 255:
            raise AssemblerError(
                f"{addr} must have a value between 0-255", line_no
            )
        code[patch_pos] = addr

    return AssembleResult(code=code, labels=labels, mapping=mapping)
