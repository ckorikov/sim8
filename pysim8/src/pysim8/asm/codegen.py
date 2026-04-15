"""Two-pass assembler (pass 1: encode, pass 2: resolve labels). Called after preprocessing (@include resolution)."""

from __future__ import annotations

import warnings
from dataclasses import dataclass, field
from pathlib import Path

from pysim8.asm._codegen_core import AssemblerError, _encode_operand, _find_instr
from pysim8.asm._codegen_fp import _encode_db, _encode_fmov_imm, _encode_fp_instruction
from pysim8.asm._codegen_vu import _encode_vu_instruction
from pysim8.asm.parser import (
    OpAddrLabel,
    OpConst,
    Operand,
    OpFpImm,
    OpFpReg,
    OpLabel,
    OpPageLabel,
    ParsedLine,
    ParseError,
    parse_lines,
)
from pysim8.asm.preprocess import PreprocessError, PreprocessResult, SourceLoc, preprocess
from pysim8.isa import (
    BY_MNEMONIC_FP,
    FP_CONTROL_MNEMONICS,
    IO_START,
    MNEMONICS_FP,
    MNEMONICS_VU,
    PAGE_SIZE,
)

__all__ = ["assemble", "AssemblerError", "AssembleResult"]


@dataclass(slots=True)
class AssembleResult:
    """Result of assembling source code."""

    code: list[int] = field(default_factory=list)
    labels: dict[str, int] = field(default_factory=dict)
    mapping: dict[int, SourceLoc] = field(default_factory=dict)


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
        if mnemonic == "FMOV" and len(operands) == 2 and isinstance(operands[1], OpFpImm):
            return _encode_fmov_imm(operands, dst_suffix, line)
        instr = _find_instr(mnemonic, operands, line, table=BY_MNEMONIC_FP)
        if mnemonic in FP_CONTROL_MNEMONICS:
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
    label_offset: int = 0


# ── Pass 1 state ─────────────────────────────────────────────────


@dataclass(slots=True)
class _Pass1State:
    """Mutable state accumulated during Pass 1."""

    page_codes: dict[int, list[int]] = field(default_factory=lambda: {0: []})
    page_cursors: dict[int, int] = field(default_factory=lambda: {0: 0})
    current_page: int = 0
    seen_pages: set[int] = field(default_factory=lambda: {0})
    has_page_directive: bool = False
    label_info: dict[str, tuple[int, int]] = field(default_factory=dict)
    page_mapping: dict[tuple[int, int], SourceLoc] = field(default_factory=dict)
    patches: list[LabelPatch] = field(default_factory=list)
    page_locs: dict[int, SourceLoc] = field(default_factory=dict)


# ── Pass 1: code generation ──────────────────────────────────────


def _pass1_handle_page(
    state: _Pass1State,
    operands: list[Operand],
    loc: SourceLoc,
) -> None:
    """Handle @PAGE directive."""
    state.has_page_directive = True
    if not operands or not isinstance(operands[0], OpConst):
        raise AssemblerError("@page: internal error (bad operand)", loc[1], filename=loc[0])
    page_num = operands[0].value
    filename, orig_line = loc

    if page_num not in state.seen_pages:
        state.seen_pages.add(page_num)
        state.page_codes[page_num] = []
        state.page_cursors[page_num] = 0

    state.current_page = page_num
    state.page_locs[page_num] = loc

    if len(operands) > 1:
        if not isinstance(operands[1], OpConst):
            raise AssemblerError("@page: internal error (bad offset operand)", orig_line, filename=filename)
        target_offset = operands[1].value
        current_len = len(state.page_codes[page_num])
        if target_offset > current_len:
            state.page_codes[page_num].extend([0] * (target_offset - current_len))
        state.page_cursors[page_num] = target_offset


def _label_patch_pos(
    operands: list[Operand],
    i: int,
    mnemonic: str,
    pos: int,
    arch: int,
) -> int:
    """Compute the byte offset for a label patch in the encoded output."""
    is_fp_data = arch >= 2 and mnemonic in MNEMONICS_FP and mnemonic not in FP_CONTROL_MNEMONICS
    if is_fp_data:
        fp_count = sum(1 for o in operands if isinstance(o, OpFpReg))
        non_fp_idx = sum(1 for o in operands[:i] if not isinstance(o, OpFpReg))
        return pos + 1 + fp_count + non_fp_idx
    if mnemonic == "VSET":
        if len(operands) == 3:
            return pos + 3 if i == 1 else pos + 2
        return pos + 2  # OpAddrLabel case
    return pos + 1 + i


def _pass1_collect_patches(
    state: _Pass1State,
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
        # VSET 2-op bare label: emit lo patch (pos+2) + hi patch (pos+3)
        if mnemonic == "VSET" and len(operands) == 2 and isinstance(op, OpLabel):
            state.patches.append(LabelPatch(state.current_page, pos + 2, op.name, False, is_jump, loc))
            state.patches.append(LabelPatch(state.current_page, pos + 3, op.name, True, is_jump, loc))
            continue
        patch_pos = _label_patch_pos(operands, i, mnemonic, pos, arch)
        lbl_off = op.offset if isinstance(op, OpAddrLabel) else 0
        state.patches.append(LabelPatch(state.current_page, patch_pos, op.name, is_page_ref, is_jump, loc, lbl_off))


def _pass1(parsed: list[ParsedLine], prep: PreprocessResult, arch: int) -> _Pass1State:
    """Pass 1: generate code, collect labels and patches."""
    state = _Pass1State()

    for pline in parsed:
        loc = prep.line_map.get(pline.line_no, (None, pline.line_no))

        if pline.label is not None:
            pos = state.page_cursors[state.current_page]
            state.label_info[pline.label] = (state.current_page, pos)

        if pline.mnemonic is None:
            continue

        if pline.mnemonic == "@PAGE":
            _pass1_handle_page(state, pline.operands or [], loc)
            continue

        operands = pline.operands if pline.operands is not None else []
        page = state.current_page
        pos = state.page_cursors[page]

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
            state.page_mapping[(page, pos)] = loc

        _pass1_collect_patches(
            state,
            operands,
            pos,
            pline.mnemonic,
            pline.mnemonic in _JUMP_MNEMONICS,
            loc,
            arch,
        )

        codes = state.page_codes[page]
        end = pos + len(encoded)
        if end <= len(codes):
            codes[pos:end] = encoded
        else:
            if pos < len(codes):
                codes[pos:] = encoded
            else:
                codes.extend(encoded)
        state.page_cursors[page] = end

    return state


# ── Page overflow check ──────────────────────────────────────────


def _validate_page_overflow(state: _Pass1State) -> None:
    """Check page size limits (only when @page directives are present)."""
    if not state.has_page_directive:
        return
    for page, data in state.page_codes.items():
        if len(data) > PAGE_SIZE:
            filename, line = state.page_locs.get(page, (None, 1))
            raise AssemblerError(
                f"Page {page} overflow: {len(data)} bytes exceeds {PAGE_SIZE}",
                line,
                filename=filename,
            )
    if 0 in state.page_codes and len(state.page_codes[0]) > IO_START:
        warnings.warn(
            f"Page 0 output is {len(state.page_codes[0])} bytes; I/O region ({IO_START}-{PAGE_SIZE - 1}) will be overwritten",
            stacklevel=3,
        )


# ── Pass 2: label resolution ─────────────────────────────────────


def _pass2(state: _Pass1State) -> None:
    """Resolve label references and validate cross-page jumps."""
    for patch in state.patches:
        patch_page, patch_pos, label_name = patch.page, patch.pos, patch.name
        is_page_ref, is_jump = patch.is_page_ref, patch.is_jump
        filename, orig_line = patch.loc
        if label_name not in state.label_info:
            raise AssemblerError(f"Undefined label: {label_name}", orig_line, filename=filename)
        label_page, label_offset = state.label_info[label_name]
        resolved = label_offset + patch.label_offset

        if is_page_ref:
            state.page_codes[patch_page][patch_pos] = label_page
            continue
        if resolved < 0 or resolved > 255:
            raise AssemblerError(
                f"[{label_name} + {patch.label_offset}]: resolved address {resolved} out of range 0-255",
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
            raise AssemblerError(
                f"cross-page jump from page {patch_page} to page {label_page}",
                orig_line,
                filename=filename,
            )
        state.page_codes[patch_page][patch_pos] = resolved


# ── Build output ─────────────────────────────────────────────────


def _build_output(state: _Pass1State) -> AssembleResult:
    """Flatten page codes into final AssembleResult."""
    multi = state.has_page_directive

    if multi:
        max_page = max(state.page_codes.keys())
        code: list[int] = [0] * ((max_page + 1) * PAGE_SIZE)
        for page, data in state.page_codes.items():
            base = page * PAGE_SIZE
            for i, b in enumerate(data):
                code[base + i] = b
    else:
        code = state.page_codes[0]

    def flat(p: int, o: int) -> int:
        return p * PAGE_SIZE + o if multi else o

    labels: dict[str, int] = {}
    for name, (page, offset) in state.label_info.items():
        labels[name] = flat(page, offset)

    mapping: dict[int, SourceLoc] = {}
    for (page, offset), loc in state.page_mapping.items():
        mapping[flat(page, offset)] = loc

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
    try:
        prep = preprocess(source, base_path, include_paths=include_paths)
    except PreprocessError as e:
        raise AssemblerError(e.message, e.line, filename=e.filename) from e

    try:
        parsed = parse_lines(prep.source, arch=arch)
    except ParseError as e:
        filename, orig_line = prep.line_map.get(e.line, (None, e.line))
        raise AssemblerError(e.message, orig_line, filename=filename) from e

    state = _pass1(parsed, prep, arch)
    _validate_page_overflow(state)
    _pass2(state)

    return _build_output(state)
