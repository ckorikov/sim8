"""Two-pass assembler (pass 1: encode, pass 2: resolve labels). Called after preprocessing (@include resolution)."""

from __future__ import annotations

import warnings
from collections.abc import Mapping
from dataclasses import dataclass, field
from pathlib import Path

from pysim8.asm.parser import (
    AsmError,
    OpAddr,
    OpAddrLabel,
    OpConst,
    Operand,
    OpFloat,
    OpFpImm,
    OpFpReg,
    OpLabel,
    OpPageLabel,
    OpReg,
    OpRegAddr,
    OpString,
    OpVuReg,
    ParsedLine,
    ParseError,
    parse_lines,
)
from pysim8.asm.preprocess import PreprocessError, PreprocessResult, SourceLoc, preprocess
from pysim8.fp_formats import FpExceptions, float_to_bytes
from pysim8.isa import (
    ARITH_CODES,
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    FP_CONTROL_MNEMONICS,
    FP_FMT_O3,
    FP_FMT_WIDTH,
    FP_SUFFIX_TO_FMT,
    FP_WIDTH_REGS,
    GPR_CODES,
    IO_START,
    ISA_VU,
    MNEMONICS_FP,
    MNEMONICS_VU,
    PAGE_SIZE,
    STACK_CODES,
    VU_CMP_SUFFIX,
    VU_FMT_ELEM_SIZE,
    VU_MODE_R,
    VU_MODE_VI,
    VU_MODE_VS,
    VU_MODE_VV,
    VU_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_MODE,
    VU_SYNC_MNEMONICS,
    InstrDef,
    Op,
    OpType,
    encode_fpm,
    encode_regaddr,
    encode_vfm,
    encode_vu_regs,
)

__all__ = ["assemble", "AssemblerError", "AssembleResult"]


class AssemblerError(AsmError):
    """Assembler error (encoding/resolution phase)."""


@dataclass(slots=True)
class AssembleResult:
    """Result of assembling source code."""

    code: list[int] = field(default_factory=list)
    labels: dict[str, int] = field(default_factory=dict)
    mapping: dict[int, SourceLoc] = field(default_factory=dict)


# ── Operand matching and encoding ──────────────────────────────────


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
        if len(instr.sig) != len(operands):
            continue
        if all(_operand_matches(op, ot) for op, ot in zip(operands, instr.sig)):
            return instr

    max_arity = max(len(i.sig) for i in candidates)
    if len(operands) > max_arity:
        raise AssemblerError(f"{mnemonic}: too many arguments", line)
    raise AssemblerError(f"{mnemonic} does not support this operand(s)", line)


# ── DB encoding ────────────────────────────────────────────────────


def _encode_db_operand(
    op: Operand,
    line: int,
    result: list[int],
) -> None:
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
    """Resolve and validate FP format suffix to fmt code."""
    upper = suffix.upper()
    if upper not in FP_SUFFIX_TO_FMT:
        raise AssemblerError(f"Invalid FP format suffix: .{suffix}", line)
    return FP_SUFFIX_TO_FMT[upper]


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
    # Determine format code(s) from suffix
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
        dst_fpm = encode_fpm(dst_reg.phys, dst_reg.pos, dst_fmt)
        src_fpm = encode_fpm(src_reg.phys, src_reg.pos, src_fmt)
        return [int(instr.op), dst_fpm, src_fpm]

    if dst_fmt is None:
        raise AssemblerError("FP instruction requires a format suffix", line)

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
    fpm_bytes = [encode_fpm(fp_op.phys, fp_op.pos, dst_fmt) for fp_op in fp_ops]

    # Encode non-FP bytes
    non_fp_bytes = [_encode_operand(op) for op in non_fp_ops]

    return [int(instr.op)] + fpm_bytes + non_fp_bytes


# ── FMOV immediate encoding ──────────────────────────────────────


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

    fpm_byte = encode_fpm(dst_reg.phys, dst_reg.pos, dst_fmt)

    if fmt_width == 8:
        return [int(Op.FMOV_FP_IMM8), fpm_byte, data[0]]
    else:
        return [int(Op.FMOV_FP_IMM16), fpm_byte, data[0], data[1]]


# ── VU instruction encoding ───────────────────────────────────────


def _encode_vu_instruction(
    mnemonic: str,
    operands: list[Operand],
    dst_suffix: str | None,
    src_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode one VU instruction into bytes."""
    # Synchronous: VSET, VFSTAT, VFCLR, VWAIT
    if mnemonic in VU_SYNC_MNEMONICS:
        return _encode_vu_sync(mnemonic, operands, line)

    # Asynchronous: VADD..VFILL
    return _encode_vu_async(mnemonic, operands, dst_suffix, src_suffix, line)


def _encode_vu_sync(mnemonic: str, operands: list[Operand], line: int) -> list[int]:
    """Encode synchronous VU instruction."""
    if mnemonic == "VFCLR":
        return [int(Op.VFCLR)]
    if mnemonic == "VWAIT":
        return [int(Op.VWAIT)]
    if mnemonic == "VFSTAT":
        if len(operands) != 1 or not isinstance(operands[0], OpReg):
            raise AssemblerError("VFSTAT requires one GPR operand", line)
        if operands[0].code > 3:
            raise AssemblerError("VFSTAT requires GPR A-D", line)
        return [int(Op.VFSTAT), operands[0].code]
    if mnemonic == "VSET":
        return _encode_vset(operands, line)
    raise AssemblerError(f"Unknown VU sync instruction: {mnemonic}", line)


_VSET_BYTE_EXPR = (OpConst, OpLabel, OpPageLabel, OpAddrLabel)


def _encode_vset(operands: list[Operand], line: int) -> list[int]:
    """Encode VSET instruction (4 forms: imm16, gpr-pair, mem, memi)."""
    if len(operands) < 2:
        raise AssemblerError("VSET requires at least 2 operands", line)
    if not isinstance(operands[0], OpVuReg):
        raise AssemblerError("VSET first operand must be a VU register", line)
    target = operands[0].code

    # VSET reg, rH, rL (opcode 164) — GPR pair; must come before composite check
    if len(operands) == 3 and isinstance(operands[1], OpReg) and isinstance(operands[2], OpReg):
        rh, rl = operands[1].code, operands[2].code
        if rh > 3 or rl > 3:
            raise AssemblerError("VSET GPR pair requires A-D", line)
        return [int(Op.VSET_GPR), target, (rh << 2) | rl]

    # VSET reg, gpr (opcode 164) — single GPR, zero-extended to 16-bit (bit 4 flag)
    if len(operands) == 2 and isinstance(operands[1], OpReg):
        gpr = operands[1].code
        if gpr > 3:
            raise AssemblerError("VSET single GPR requires A-D", line)
        return [int(Op.VSET_GPR), target, 0x10 | gpr]

    # VSET reg, hi, lo (opcode 163) — composite byte-expression pair
    if len(operands) == 3 and isinstance(operands[1], _VSET_BYTE_EXPR) and isinstance(operands[2], _VSET_BYTE_EXPR):
        hi_val = operands[1].value if isinstance(operands[1], OpConst) else 0
        lo_val = operands[2].value if isinstance(operands[2], OpConst) else 0
        if isinstance(operands[1], OpConst) and not 0 <= hi_val <= 255:
            raise AssemblerError(f"VSET composite hi operand out of range: {hi_val}", line)
        if isinstance(operands[2], OpConst) and not 0 <= lo_val <= 255:
            raise AssemblerError(f"VSET composite lo operand out of range: {lo_val}", line)
        return [int(Op.VSET_IMM16), target, lo_val & 0xFF, hi_val & 0xFF]

    # VSET reg, imm16 (opcode 163) — single numeric immediate, 0–65535
    if len(operands) == 2 and isinstance(operands[1], OpConst):
        val = operands[1].value
        if val < 0 or val > 65535:
            raise AssemblerError(f"VSET immediate must be 0-65535, got {val}", line)
        return [int(Op.VSET_IMM16), target, val & 0xFF, (val >> 8) & 0xFF]

    # VSET reg, label (opcode 163) — full 16-bit address: lo=offset(label), hi=page(label), two patches emitted in pass 1
    if len(operands) == 2 and isinstance(operands[1], OpLabel):
        return [int(Op.VSET_IMM16), target, 0, 0]

    # VSET reg, [addr] / [label] (opcode 165) — read 16-bit LE from DP×256+addr
    if len(operands) == 2 and isinstance(operands[1], (OpAddr, OpAddrLabel)):
        addr = operands[1].value if isinstance(operands[1], OpAddr) else 0
        return [int(Op.VSET_MEM), target, addr]

    # VSET reg, [reg±offset] (opcode 166)
    if len(operands) == 2 and isinstance(operands[1], OpRegAddr):
        return [int(Op.VSET_MEMI), target, encode_regaddr(operands[1].reg_code, operands[1].offset)]

    raise AssemblerError("VSET does not support this operand(s)", line)


_VU_MNEMONIC_TO_OP: dict[str, int] = {d.mnemonic: int(d.op) for d in ISA_VU if d.mnemonic not in VU_SYNC_MNEMONICS}
# VFILL is an alias for VMOV — emits opcode 182 (Op.VMOV) with forced vi mode
_VU_MNEMONIC_TO_OP["VFILL"] = int(Op.VMOV)

_VU_SINGLE_MODE: frozenset[str] = frozenset({"VDOT", "VSQRT", "VNEG", "VABS", "VSEL"})


def _resolve_vu_mode_cond(
    mnemonic: str,
    mode_suffix: str | None,
    operands: list[Operand],
    line: int,
) -> tuple[int, int]:
    """Resolve VU mode and condition from mnemonic, suffix, and operands.

    Mode is inferred from operand types when suffix is omitted.
    """
    if mnemonic == "VCMP":
        if mode_suffix is None:
            raise AssemblerError("VCMP requires a condition suffix", line)
        cond_upper = mode_suffix.upper()
        if cond_upper not in VU_CMP_SUFFIX:
            raise AssemblerError(f"Invalid VCMP condition: .{mode_suffix}", line)
        return 0, VU_CMP_SUFFIX[cond_upper]
    if mnemonic == "VFILL":
        return VU_MODE_VI, 0
    if mnemonic in _VU_SINGLE_MODE:
        return 0, 0
    # Explicit suffix takes priority
    if mode_suffix is not None:
        mode_upper = mode_suffix.upper()
        if mode_upper not in VU_SUFFIX_TO_MODE:
            raise AssemblerError(f"Invalid VU mode suffix: .{mode_suffix}", line)
        return VU_SUFFIX_TO_MODE[mode_upper], 0
    # Infer from operands
    non_vu = [op for op in operands if not isinstance(op, OpVuReg)]
    has_gpr = any(isinstance(op, OpReg) for op in non_vu)
    has_imm = any(isinstance(op, OpConst) for op in non_vu)
    vu_count = sum(1 for op in operands if isinstance(op, OpVuReg))
    if has_gpr:
        return VU_MODE_VS, 0
    if has_imm:
        return VU_MODE_VI, 0
    if vu_count <= 2:
        return VU_MODE_R, 0
    return VU_MODE_VV, 0


def _resolve_vu_fmt(mnemonic: str, fmt_suffix: str | None, line: int) -> int:
    """Validate and resolve VU format suffix to fmt code."""
    if fmt_suffix is None:
        raise AssemblerError(f"{mnemonic} requires a format suffix", line)
    fmt_upper = fmt_suffix.upper()
    if fmt_upper not in VU_SUFFIX_TO_FMT:
        raise AssemblerError(f"Invalid VU format suffix: .{fmt_suffix}", line)
    return VU_SUFFIX_TO_FMT[fmt_upper]


def _encode_vu_regs_from_operands(operands: list[Operand], mnemonic: str, mode: int, line: int) -> int:
    """Extract and validate VU pointer registers from operands, return encoded byte.

    For mode=VS (GPR broadcast), src2 encodes the GPR code instead of VU register.
    """
    vu_regs = [op for op in operands if isinstance(op, OpVuReg)]
    if not vu_regs:
        raise AssemblerError(f"{mnemonic} requires VU register operands", line)
    for r in vu_regs:
        if r.code > 3:
            raise AssemblerError("Async VU operands must be pointer registers (VA-VM)", line)
    dc = vu_regs[0].code
    s1c = vu_regs[1].code if len(vu_regs) > 1 else 0
    if mode == VU_MODE_VS:
        gpr_ops = [op for op in operands if isinstance(op, OpReg)]
        if not gpr_ops:
            raise AssemblerError(f"{mnemonic} broadcast requires a GPR operand (A-D)", line)
        gpr_code = gpr_ops[0].code
        if gpr_code > 3:
            raise AssemblerError("Broadcast GPR must be A-D", line)
        s2c = gpr_code
    else:
        s2c = vu_regs[2].code if len(vu_regs) > 2 else 0
    return encode_vu_regs(dc, s1c, s2c)


def _encode_vu_async(
    mnemonic: str,
    operands: list[Operand],
    fmt_suffix: str | None,
    mode_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode asynchronous VU instruction."""
    opcode = _VU_MNEMONIC_TO_OP.get(mnemonic)
    if opcode is None:
        raise AssemblerError(f"Unknown VU async instruction: {mnemonic}", line)

    fmt = _resolve_vu_fmt(mnemonic, fmt_suffix, line)
    mode, cond = _resolve_vu_mode_cond(mnemonic, mode_suffix, operands, line)

    # GPR broadcast restricted to byte formats
    if mode == VU_MODE_VS and VU_FMT_ELEM_SIZE.get(fmt, 1) > 1:
        raise AssemblerError(f"GPR broadcast only for byte formats (U/I/O3/O2), not .{fmt_suffix}", line)

    regs_byte = _encode_vu_regs_from_operands(operands, mnemonic, mode, line)
    result = [opcode, encode_vfm(fmt, mode), regs_byte]

    if mnemonic == "VCMP":
        result.append(cond)

    if mode == VU_MODE_VI:
        imm_ops = [op for op in operands if isinstance(op, OpConst)]
        if not imm_ops:
            raise AssemblerError(f"{mnemonic} requires an immediate operand", line)
        imm_val = imm_ops[0].value
        elem_sz = VU_FMT_ELEM_SIZE.get(fmt, 1)
        for i in range(elem_sz):
            result.append((imm_val >> (8 * i)) & 0xFF)

    return result


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

    if arch >= 3 and mnemonic in MNEMONICS_VU:
        return _encode_vu_instruction(mnemonic, operands, dst_suffix, src_suffix, line)

    if arch >= 2 and mnemonic in MNEMONICS_FP:
        # FMOV immediate special case (bypasses _find_fp_insn)
        if mnemonic == "FMOV" and len(operands) == 2 and isinstance(operands[1], OpFpImm):
            return _encode_fmov_imm(operands, dst_suffix, line)

        instr = _find_instr(mnemonic, operands, line, table=BY_MNEMONIC_FP)
        if mnemonic in FP_CONTROL_MNEMONICS:
            # Control: no FPM, just opcode + operand bytes
            return [int(instr.op)] + [_encode_operand(op) for op in operands]
        return _encode_fp_instruction(instr, operands, dst_suffix, src_suffix, line)

    instr = _find_instr(mnemonic, operands, line)
    return [int(instr.op)] + [_encode_operand(op) for op in operands]


# ── Jump/call mnemonics (for cross-page validation) ──────────────

_JUMP_MNEMONICS = frozenset({"JMP", "JC", "JNC", "JZ", "JNZ", "JA", "JNA", "CALL"})

# ── Patch descriptor ─────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class LabelPatch:
    """Describes a label reference that needs resolution in Pass 2."""

    page: int
    pos: int
    name: str
    is_page_ref: bool
    is_jump: bool
    loc: SourceLoc


# ── Pass 1 state ─────────────────────────────────────────────────


@dataclass(slots=True)
class _Pass1State:
    """Mutable state accumulated during Pass 1."""

    page_codes: dict[int, list[int]] = field(default_factory=lambda: {0: []})
    current_page: int = 0
    seen_pages: set[int] = field(default_factory=lambda: {0})
    has_page_directive: bool = False
    label_info: dict[str, tuple[int, int]] = field(default_factory=dict)
    page_mapping: dict[tuple[int, int], SourceLoc] = field(default_factory=dict)
    label_patches: list[LabelPatch] = field(default_factory=list)
    page_locs: dict[int, SourceLoc] = field(default_factory=dict)


# ── Pass 1: code generation ──────────────────────────────────────


def _pass1_handle_page(
    st: _Pass1State,
    operands: list[Operand],
    loc: SourceLoc,
) -> None:
    """Handle @PAGE directive."""
    st.has_page_directive = True
    if not operands or not isinstance(operands[0], OpConst):
        raise AssemblerError("@page: internal error (bad operand)", loc[1], filename=loc[0])
    page_num = operands[0].value
    filename, orig_line = loc

    if page_num not in st.seen_pages:
        st.seen_pages.add(page_num)
        st.page_codes[page_num] = []

    st.current_page = page_num
    st.page_locs[page_num] = loc

    # Handle optional offset
    if len(operands) > 1:
        if not isinstance(operands[1], OpConst):
            raise AssemblerError("@page: internal error (bad offset operand)", orig_line, filename=filename)
        target_offset = operands[1].value
        current_len = len(st.page_codes[page_num])
        if target_offset < current_len:
            raise AssemblerError(
                f"@page {page_num}: offset {target_offset} is before current position {current_len}",
                orig_line,
                filename=filename,
            )
        # Pad with zeros to reach target offset
        st.page_codes[page_num].extend([0] * (target_offset - current_len))


def _pass1_collect_label_patches(
    st: _Pass1State,
    operands: list[Operand],
    pos: int,
    mnemonic: str,
    is_jump: bool,
    loc: SourceLoc,
    arch: int,
) -> None:
    """Record label references that need resolution in Pass 2."""
    for i, op in enumerate(operands):
        if not isinstance(op, (OpLabel, OpAddrLabel, OpPageLabel)):
            continue
        is_page_ref = isinstance(op, OpPageLabel)
        # For FP data instructions, FPM bytes are reordered before non-FP bytes.
        is_fp_data = arch >= 2 and mnemonic in MNEMONICS_FP and mnemonic not in FP_CONTROL_MNEMONICS
        if is_fp_data:
            fp_count = sum(1 for o in operands if isinstance(o, OpFpReg))
            non_fp_idx = sum(1 for o in operands[:i] if not isinstance(o, OpFpReg))
            patch_pos = pos + 1 + fp_count + non_fp_idx
        elif mnemonic == "VSET":
            # 3-op [VSET_IMM16, target, lo, hi]: operand[1]=hi at pos+3, operand[2]=lo at pos+2
            # 2-op bare label: auto-expand to full 16-bit — emit lo patch (pos+2) + hi patch (pos+3)
            # 2-op [VSET_MEM, target, addr]: addr at pos+2
            if len(operands) == 3:
                patch_pos = pos + 3 if i == 1 else pos + 2
            elif isinstance(op, OpLabel):
                st.label_patches.append(LabelPatch(st.current_page, pos + 2, op.name, False, is_jump, loc))
                st.label_patches.append(LabelPatch(st.current_page, pos + 3, op.name, True, is_jump, loc))
                continue
            else:
                patch_pos = pos + 2
        else:
            patch_pos = pos + 1 + i
        st.label_patches.append(LabelPatch(st.current_page, patch_pos, op.name, is_page_ref, is_jump, loc))


def _pass1(parsed: list[ParsedLine], prep: PreprocessResult, arch: int) -> _Pass1State:
    """Pass 1: generate code, collect labels and patches."""
    st = _Pass1State()

    for pline in parsed:
        loc = prep.line_map.get(pline.line_no, (None, pline.line_no))

        if pline.label is not None:
            pos = len(st.page_codes[st.current_page])
            st.label_info[pline.label] = (st.current_page, pos)

        if pline.mnemonic is None:
            continue

        if pline.mnemonic == "@PAGE":
            _pass1_handle_page(st, pline.operands or [], loc)
            continue

        operands = pline.operands if pline.operands is not None else []
        pos = len(st.page_codes[st.current_page])

        try:
            encoded = _encode_instruction(
                pline.mnemonic,
                operands,
                pline.line_no,
                dst_suffix=pline.dst_suffix,
                src_suffix=pline.src_suffix,
                arch=arch,
            )
        except AssemblerError as e:
            filename, orig_line = loc
            raise AssemblerError(e.message, orig_line, filename=filename) from e

        if pline.mnemonic != "DB":
            st.page_mapping[(st.current_page, pos)] = loc

        _pass1_collect_label_patches(
            st,
            operands,
            pos,
            pline.mnemonic,
            pline.mnemonic in _JUMP_MNEMONICS,
            loc,
            arch,
        )

        st.page_codes[st.current_page].extend(encoded)

    return st


# ── Page overflow check ──────────────────────────────────────────


def _check_page_overflow(st: _Pass1State) -> None:
    """Check page size limits (only when @page directives are present)."""
    if not st.has_page_directive:
        return
    for page, data in st.page_codes.items():
        if len(data) > PAGE_SIZE:
            filename, line = st.page_locs.get(page, (None, 1))
            raise AssemblerError(
                f"Page {page} overflow: {len(data)} bytes exceeds {PAGE_SIZE}",
                line,
                filename=filename,
            )
    if 0 in st.page_codes and len(st.page_codes[0]) > IO_START:
        warnings.warn(
            f"Page 0 output is {len(st.page_codes[0])} bytes; I/O region ({IO_START}-{PAGE_SIZE - 1}) will be overwritten",
            stacklevel=3,
        )


# ── Pass 2: label resolution ─────────────────────────────────────


def _pass2(st: _Pass1State) -> None:
    """Resolve label references and validate cross-page jumps."""
    for patch in st.label_patches:
        patch_page, patch_pos, label_name = patch.page, patch.pos, patch.name
        is_page_ref, is_jump = patch.is_page_ref, patch.is_jump
        filename, orig_line = patch.loc
        if label_name not in st.label_info:
            raise AssemblerError(f"Undefined label: {label_name}", orig_line, filename=filename)
        label_page, label_offset = st.label_info[label_name]

        if is_page_ref:
            st.page_codes[patch_page][patch_pos] = label_page
        else:
            if label_offset < 0 or label_offset > 255:
                raise AssemblerError(
                    f"{label_offset} must have a value between 0-255",
                    orig_line,
                    filename=filename,
                )
            if is_jump and label_page != patch_page:
                if patch_page == 0:
                    raise AssemblerError(
                        f"jump target '{label_name}' is on page {label_page}, but IP executes only on page 0",
                        orig_line,
                        filename=filename,
                    )
                else:
                    raise AssemblerError(
                        f"cross-page jump from page {patch_page} to page {label_page}",
                        orig_line,
                        filename=filename,
                    )
            st.page_codes[patch_page][patch_pos] = label_offset


# ── Build output ─────────────────────────────────────────────────


def _build_output(st: _Pass1State) -> AssembleResult:
    """Flatten page codes into final AssembleResult."""
    multi = st.has_page_directive

    # Flatten code
    if multi:
        max_page = max(st.page_codes.keys())
        code: list[int] = [0] * ((max_page + 1) * PAGE_SIZE)
        for page, data in st.page_codes.items():
            base = page * PAGE_SIZE
            for i, b in enumerate(data):
                code[base + i] = b
    else:
        code = st.page_codes[0]

    # Labels: name → memory address
    labels: dict[str, int] = {}
    for name, (page, offset) in st.label_info.items():
        labels[name] = page * PAGE_SIZE + offset if multi else offset

    # Mapping: flat code position → SourceLoc
    mapping: dict[int, SourceLoc] = {}
    for (page, offset), loc in st.page_mapping.items():
        flat_pos = page * PAGE_SIZE + offset if multi else offset
        mapping[flat_pos] = loc

    return AssembleResult(code=code, labels=labels, mapping=mapping)


# ── Main entry point ─────────────────────────────────────────────


def assemble(
    source: str,
    arch: int = 1,
    base_path: Path | None = None,
    include_paths: list[Path] | None = None,
) -> AssembleResult:
    """Assemble source code into machine code.

    Pipeline: Phase 0 (preprocessing) → Pass 1 (codegen) → Pass 2 (label resolution).

    Args:
        source: Assembly source text.
        arch: Architecture version (1=integer-only, 2=with FPU, 3=FPU+VU). Default 1.
        base_path: Directory for resolving @include paths.
        include_paths: Additional search directories for @include (like -I in C).

    Returns AssembleResult with code, labels, and source mapping.
    """
    # Phase 0: preprocessing (@include resolution)
    try:
        prep = preprocess(source, base_path, include_paths=include_paths)
    except PreprocessError as e:
        raise AssemblerError(e.message, e.line, filename=e.filename) from e

    try:
        parsed = parse_lines(prep.source, arch=arch)
    except ParseError as e:
        filename, orig_line = prep.line_map.get(e.line, (None, e.line))
        raise AssemblerError(e.message, orig_line, filename=filename) from e

    # Pass 1: generate code, collect labels
    st = _pass1(parsed, prep, arch)

    # Page overflow check (multi-page only)
    _check_page_overflow(st)

    # Pass 2: resolve labels
    _pass2(st)

    return _build_output(st)
