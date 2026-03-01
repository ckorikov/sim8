"""Two-pass assembler: parse → encode → resolve labels."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field

from pysim8.isa import (
    OpType, Reg, InsnDef, BY_MNEMONIC, BY_MNEMONIC_FP, MNEMONICS_FP,
    FP_CONTROL_MNEMONICS, GPR_CODES, STACK_CODES, encode_regaddr,
    encode_fpm, FP_REGISTERS, FP_SUFFIX_TO_FMT, FP_FMT_WIDTH,
    FP_WIDTH_REGS, FP_FMT_N1, FP_FMT_N2, Op,
)
from pysim8.asm.parser import (
    AsmError,
    OpReg,
    OpConst,
    OpAddr,
    OpAddrLabel,
    OpRegAddr,
    OpString,
    OpLabel,
    OpFpReg,
    OpFloat,
    OpFpImm,
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


def _operand_matches(op: Operand, ot: OpType) -> bool:
    """Check if a parsed operand matches an ISA operand type."""
    match ot:
        case OpType.REG:
            return isinstance(op, OpReg)
        case OpType.REG_STACK:
            return isinstance(op, OpReg) and op.code in STACK_CODES
        case OpType.REG_GPR:
            return isinstance(op, OpReg) and op.code in GPR_CODES
        case OpType.IMM:
            return isinstance(op, (OpConst, OpLabel))
        case OpType.MEM:
            return isinstance(op, (OpAddr, OpAddrLabel))
        case OpType.REGADDR:
            return isinstance(op, OpRegAddr)
        case OpType.FP_REG:
            return isinstance(op, OpFpReg)
        case OpType.FP_IMM8 | OpType.FP_IMM16:
            return isinstance(op, OpFpImm)
    return False


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
        case OpAddrLabel():
            return 0  # placeholder for pass 2
    raise AssertionError(f"unexpected operand: {op!r}")


def _find_insn(
    mnemonic: str,
    operands: list[Operand],
    line: int,
    table: Mapping[str, tuple[InsnDef, ...]] | None = None,
) -> InsnDef:
    """Find matching InsnDef by mnemonic and operands."""
    if table is None:
        table = BY_MNEMONIC
    candidates = table.get(mnemonic)
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

    max_arity = max(len(i.sig) for i in candidates)
    if len(operands) > max_arity:
        raise AssemblerError(
            f"{mnemonic}: too many arguments", line
        )
    raise AssemblerError(
        f"{mnemonic} does not support this operand(s)", line
    )


# ── DB encoding ────────────────────────────────────────────────────


def _encode_db_operand(
    op: Operand, line: int, result: list[int],
) -> None:
    """Encode one DB operand, appending bytes to result."""
    if isinstance(op, OpConst):
        result.append(op.value)
        return
    if isinstance(op, OpString):
        if not op.text:
            raise AssemblerError(
                "DB string must not be empty", line
            )
        result.extend(ord(c) for c in op.text)
        return
    if isinstance(op, OpFloat):
        from pysim8.fp_formats import float_to_bytes
        data, _exc = float_to_bytes(op.value, op.fmt)
        result.extend(data)
        return
    raise AssemblerError(
        f"DB does not support this operand: {op!r}", line
    )


def _encode_db(operands: list[Operand], line: int) -> list[int]:
    """Encode DB pseudo-instruction."""
    result: list[int] = []
    for op in operands:
        _encode_db_operand(op, line, result)
    return result


# ── FP instruction encoding ──────────────────────────────────────


def _validate_fp_suffix(suffix: str, line: int) -> int:
    """Resolve and validate FP format suffix to fmt code."""
    upper = suffix.upper()
    if upper not in FP_SUFFIX_TO_FMT:
        raise AssemblerError(
            f"Invalid FP format suffix: .{suffix}", line
        )
    return FP_SUFFIX_TO_FMT[upper]


def _validate_fp_reg_width(
    reg: OpFpReg, fmt: int, line: int
) -> None:
    """Check that register width matches format width."""
    fmt_width = FP_FMT_WIDTH[fmt]
    allowed = FP_WIDTH_REGS.get(fmt_width, frozenset())
    if reg.name not in allowed:
        raise AssemblerError(
            "FP format suffix does not match register width",
            line,
        )


def _find_fp_insn(
    mnemonic: str, operands: list[Operand], line: int
) -> InsnDef:
    """Find matching FP InsnDef by mnemonic and operands."""
    return _find_insn(mnemonic, operands, line, table=BY_MNEMONIC_FP)


def _encode_fp_instruction(
    insn: InsnDef,
    operands: list[Operand],
    dst_suffix: str | None,
    src_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode one FP instruction into bytes.

    FPM bytes always come before non-FP bytes in encoding,
    regardless of assembly operand order.
    """
    # Determine format code(s) from suffix
    dst_fmt = _validate_fp_suffix(dst_suffix, line) if dst_suffix else None
    src_fmt = _validate_fp_suffix(src_suffix, line) if src_suffix else None

    # FCVT special case: dual suffix
    if insn.op == Op.FCVT_FP_FP:
        assert dst_fmt is not None and src_fmt is not None
        if dst_fmt == src_fmt:
            raise AssemblerError(
                "FCVT with identical formats (use FMOV)", line
            )
        dst_reg = operands[0]
        src_reg = operands[1]
        assert isinstance(dst_reg, OpFpReg) and isinstance(src_reg, OpFpReg)
        _validate_fp_reg_width(dst_reg, dst_fmt, line)
        _validate_fp_reg_width(src_reg, src_fmt, line)
        dst_fpm = encode_fpm(dst_reg.phys, dst_reg.pos, dst_fmt)
        src_fpm = encode_fpm(src_reg.phys, src_reg.pos, src_fmt)
        return [int(insn.op), dst_fpm, src_fpm]

    assert dst_fmt is not None

    # Separate FP reg operands from non-FP operands
    fp_ops: list[OpFpReg] = []
    non_fp_ops: list[Operand] = []
    for op in operands:
        if isinstance(op, OpFpReg):
            _validate_fp_reg_width(op, dst_fmt, line)
            fp_ops.append(op)
        else:
            non_fp_ops.append(op)

    # Encode FPM bytes
    fpm_bytes = [
        encode_fpm(fp_op.phys, fp_op.pos, dst_fmt) for fp_op in fp_ops
    ]

    # Encode non-FP bytes
    non_fp_bytes = [_encode_operand(op) for op in non_fp_ops]

    return [int(insn.op)] + fpm_bytes + non_fp_bytes


# ── FMOV immediate encoding ──────────────────────────────────────


def _encode_fmov_imm(
    operands: list[Operand],
    dst_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode FMOV with FP immediate operand."""
    if not isinstance(operands[0], OpFpReg):
        raise AssemblerError(
            "FMOV does not support this operand(s)", line
        )
    assert dst_suffix is not None

    dst_reg = operands[0]
    fp_imm = operands[1]
    assert isinstance(fp_imm, OpFpImm)

    dst_fmt = _validate_fp_suffix(dst_suffix, line)
    fmt_width = FP_FMT_WIDTH[dst_fmt]

    if fmt_width == 32:
        raise AssemblerError(
            "FP immediate not supported for float32", line
        )
    if fmt_width == 4:
        raise AssemblerError(
            "FP immediate not supported for 4-bit formats", line
        )

    # Check literal suffix matches instruction suffix
    if fp_imm.fmt is not None and fp_imm.fmt != dst_fmt:
        raise AssemblerError(
            "FP immediate suffix mismatch", line
        )

    _validate_fp_reg_width(dst_reg, dst_fmt, line)

    from pysim8.fp_formats import float_to_bytes
    data, _exc = float_to_bytes(fp_imm.value, dst_fmt)

    fpm_byte = encode_fpm(dst_reg.phys, dst_reg.pos, dst_fmt)

    if fmt_width == 8:
        return [int(Op.FMOV_FP_IMM8), fpm_byte, data[0]]
    else:
        return [int(Op.FMOV_FP_IMM16), fpm_byte, data[0], data[1]]


# ── Instruction encoding ──────────────────────────────────────────


def _encode_instruction(
    mnemonic: str,
    operands: list[Operand],
    line: int,
    dst_suffix: str | None = None,
    src_suffix: str | None = None,
    arch: int = 1,
) -> list[int]:
    """Encode one instruction into bytes."""
    if mnemonic == "DB":
        return _encode_db(operands, line)

    if arch >= 2 and mnemonic in MNEMONICS_FP:
        # FMOV immediate special case (bypasses _find_fp_insn)
        if (
            mnemonic == "FMOV"
            and len(operands) == 2
            and isinstance(operands[1], OpFpImm)
        ):
            return _encode_fmov_imm(operands, dst_suffix, line)

        insn = _find_fp_insn(mnemonic, operands, line)
        if mnemonic in FP_CONTROL_MNEMONICS:
            # Control: no FPM, just opcode + operand bytes
            return [int(insn.op)] + [
                _encode_operand(op) for op in operands
            ]
        return _encode_fp_instruction(
            insn, operands, dst_suffix, src_suffix, line
        )

    insn = _find_insn(mnemonic, operands, line)
    return [int(insn.op)] + [_encode_operand(op) for op in operands]


# ── Two-pass assembly ───────────────────────────────────────────────


def assemble(source: str, arch: int = 1) -> AssembleResult:
    """Assemble source code into machine code.

    Returns AssembleResult with:
        code — machine code bytes
        labels — label name → address
        mapping — code position → source line
    """
    try:
        parsed = parse_lines(source, arch=arch)
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

        operands = (
            pline.operands if pline.operands is not None else []
        )

        encoded = _encode_instruction(
            pline.mnemonic, operands, pline.line_no,
            dst_suffix=pline.dst_suffix, src_suffix=pline.src_suffix,
            arch=arch,
        )

        if pline.mnemonic != "DB":
            mapping[pos] = pline.line_no

        if operands:
            for i, op in enumerate(operands):
                if isinstance(op, (OpLabel, OpAddrLabel)):
                    # For FP data instructions, FPM bytes are
                    # reordered before non-FP bytes. Calculate
                    # the correct position of the label byte.
                    is_fp_data = (
                        arch >= 2
                        and pline.mnemonic in MNEMONICS_FP
                        and pline.mnemonic not in FP_CONTROL_MNEMONICS
                    )
                    if is_fp_data:
                        fp_count = sum(
                            1 for o in operands
                            if isinstance(o, OpFpReg)
                        )
                        non_fp_idx = sum(
                            1 for o in operands[:i]
                            if not isinstance(o, OpFpReg)
                        )
                        label_patches.append((
                            pos + 1 + fp_count + non_fp_idx,
                            op.name,
                            pline.line_no,
                        ))
                    else:
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
