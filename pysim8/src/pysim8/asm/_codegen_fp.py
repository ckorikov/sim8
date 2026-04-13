"""FP and DB instruction encoding helpers."""

from __future__ import annotations

from pysim8.asm._codegen_core import AssemblerError, _encode_operand, _lookup_suffix
from pysim8.asm.parser import OpConst, Operand, OpFloat, OpFpImm, OpFpReg, OpString
from pysim8.fp_formats import FpExceptions, float_to_bytes
from pysim8.isa import (
    FP_FMT_O3,
    FP_FMT_WIDTH,
    FP_SUFFIX_TO_FMT,
    FP_WIDTH_REGS,
    InstrDef,
    Op,
    encode_fpm,
)

# ── DB encoding ──────────────────────────────────────────────────


def _encode_db_operand(op: Operand, line: int, result: list[int]) -> None:
    """Encode one DB operand, appending bytes to result."""
    if isinstance(op, OpConst):
        result.append(op.value)
        return
    if isinstance(op, OpString):
        if not op.text:
            raise AssemblerError("DB string must not be empty", line)
        result.extend(ord(c) for c in op.text)
        return
    if isinstance(op, OpFloat):
        data, exc = float_to_bytes(op.value, op.fmt)
        _check_e4m3_range(exc, op.fmt, line)
        result.extend(data)
        return
    raise AssemblerError("DB does not support this operand", line)


def _encode_db(operands: list[Operand], line: int) -> list[int]:
    """Encode DB pseudo-instruction."""
    result: list[int] = []
    for op in operands:
        _encode_db_operand(op, line, result)
    return result


# ── FP instruction encoding ──────────────────────────────────────


def _validate_fp_suffix(suffix: str, line: int) -> int:
    return _lookup_suffix(suffix, FP_SUFFIX_TO_FMT, "Invalid FP format suffix", line)


def _check_e4m3_range(exc: FpExceptions, fmt: int, line: int) -> None:
    if exc.overflow and fmt == FP_FMT_O3:
        raise AssemblerError("Float value out of range for format E4M3", line)


def _validate_fp_reg_width(reg: OpFpReg, fmt: int, line: int) -> None:
    """Check that register width matches format width."""
    fmt_width = FP_FMT_WIDTH[fmt]
    allowed = FP_WIDTH_REGS.get(fmt_width, frozenset())
    if reg.name not in allowed:
        raise AssemblerError(
            "FP format suffix does not match register width",
            line,
        )


def _encode_fp_instruction(
    instr: InstrDef,
    operands: list[Operand],
    dst_suffix: str | None,
    src_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode one FP instruction into bytes.

    FPM bytes always come before non-FP bytes in encoding,
    regardless of assembly operand order.
    """
    dst_fmt = _validate_fp_suffix(dst_suffix, line) if dst_suffix else None
    src_fmt = _validate_fp_suffix(src_suffix, line) if src_suffix else None

    # FCVT special case: dual suffix
    if instr.op == Op.FCVT_FP_FP:
        if dst_fmt is None or src_fmt is None:
            raise AssemblerError("FCVT requires two format suffixes", line)
        if dst_fmt == src_fmt:
            raise AssemblerError("FCVT with identical formats (use FMOV)", line)
        dst_reg = operands[0]
        src_reg = operands[1]
        if not isinstance(dst_reg, OpFpReg) or not isinstance(src_reg, OpFpReg):
            raise AssemblerError("FCVT requires two FP register operands", line)
        _validate_fp_reg_width(dst_reg, dst_fmt, line)
        _validate_fp_reg_width(src_reg, src_fmt, line)
        dst_fpm_enc = encode_fpm(dst_reg.phys, dst_reg.pos, dst_fmt)
        src_fpm_enc = encode_fpm(src_reg.phys, src_reg.pos, src_fmt)
        return [int(instr.op), dst_fpm_enc, src_fpm_enc]

    if dst_fmt is None:
        raise AssemblerError("FP instruction requires a format suffix", line)

    fp_ops: list[OpFpReg] = []
    non_fp_ops: list[Operand] = []
    for op in operands:
        if isinstance(op, OpFpReg):
            _validate_fp_reg_width(op, dst_fmt, line)
            fp_ops.append(op)
        else:
            non_fp_ops.append(op)

    fpm_encs = [encode_fpm(fp_op.phys, fp_op.pos, dst_fmt) for fp_op in fp_ops]
    non_fp_bytes = [_encode_operand(op) for op in non_fp_ops]

    return [int(instr.op)] + fpm_encs + non_fp_bytes


def _encode_fmov_imm(
    operands: list[Operand],
    dst_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode FMOV with FP immediate operand."""
    if not isinstance(operands[0], OpFpReg):
        raise AssemblerError("FMOV does not support this operand(s)", line)
    if dst_suffix is None:
        raise AssemblerError("FMOV immediate requires a format suffix", line)

    dst_reg = operands[0]
    fp_imm = operands[1]
    if not isinstance(fp_imm, OpFpImm):
        raise AssemblerError("FMOV second operand must be a float literal", line)

    dst_fmt = _validate_fp_suffix(dst_suffix, line)
    fmt_width = FP_FMT_WIDTH[dst_fmt]

    if fmt_width == 32:
        raise AssemblerError("FP immediate not supported for float32", line)
    if fmt_width == 4:
        raise AssemblerError("FP immediate not supported for 4-bit formats", line)

    if fp_imm.fmt is not None and fp_imm.fmt != dst_fmt:
        raise AssemblerError("FP immediate suffix mismatch", line)

    _validate_fp_reg_width(dst_reg, dst_fmt, line)

    data, exc = float_to_bytes(fp_imm.value, dst_fmt)
    _check_e4m3_range(exc, dst_fmt, line)

    fpm_enc = encode_fpm(dst_reg.phys, dst_reg.pos, dst_fmt)

    if fmt_width == 8:
        return [int(Op.FMOV_FP_IMM8), fpm_enc, data[0]]
    return [int(Op.FMOV_FP_IMM16), fpm_enc, data[0], data[1]]
