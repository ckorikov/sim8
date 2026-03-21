"""Two-pass assembler (pass 1: encode, pass 2: resolve labels). Called after preprocessing (@include resolution)."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import NamedTuple

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
    MNEMONICS_FP,
    STACK_CODES,
    InstrDef,
    Op,
    OpType,
    encode_fpm,
    encode_regaddr,
)
from pysim8.sim.memory import IO_START, PAGE_SIZE

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
        assert dst_fmt is not None and src_fmt is not None
        if dst_fmt == src_fmt:
            raise AssemblerError("FCVT with identical formats (use FMOV)", line)
        dst_reg = operands[0]
        src_reg = operands[1]
        assert isinstance(dst_reg, OpFpReg) and isinstance(src_reg, OpFpReg)
        _validate_fp_reg_width(dst_reg, dst_fmt, line)
        _validate_fp_reg_width(src_reg, src_fmt, line)
        dst_fpm = encode_fpm(dst_reg.phys, dst_reg.pos, dst_fmt)
        src_fpm = encode_fpm(src_reg.phys, src_reg.pos, src_fmt)
        return [int(instr.op), dst_fpm, src_fpm]

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
    assert dst_suffix is not None

    dst_reg = operands[0]
    fp_imm = operands[1]
    assert isinstance(fp_imm, OpFpImm)

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


class LabelPatch(NamedTuple):
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
        import warnings

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
        arch: Architecture version (1=integer-only, 2=with FPU). Default 1.
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
