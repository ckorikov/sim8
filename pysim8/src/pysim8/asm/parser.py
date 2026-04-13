"""Tokenizer and parser for assembly source.

Parses each source line into a structured representation:
  - label (optional)
  - instruction mnemonic
  - typed operands (Reg, Const, Addr, RegAddr, String, FpReg, Float)
"""

from __future__ import annotations

import re

from pysim8.asm._parser_operands import (
    _RE_LABEL,
    _parse_db_operands,
    _parse_operand,
    _split_operands,
    _tokenize_line,
    _try_parse_number,
    parse_number,
)
from pysim8.asm._parser_types import (
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
)
from pysim8.isa import (
    FORBIDDEN_FP_LABEL_NAMES,
    FP_CONTROL_MNEMONICS,
    MNEMONIC_ALIASES,
    MNEMONICS,
    MNEMONICS_FP,
    MNEMONICS_VU,
    REGISTERS,
)

__all__ = [
    "ParsedLine",
    "Operand",
    "OpReg",
    "OpConst",
    "OpAddr",
    "OpRegAddr",
    "OpString",
    "OpLabel",
    "OpAddrLabel",
    "OpPageLabel",
    "OpFpReg",
    "OpFloat",
    "OpFpImm",
    "OpVuReg",
    "parse_lines",
    "AsmError",
    "ParseError",
    "parse_number",
]

_ZERO_ARG_MNEMONICS: frozenset[str] = frozenset({"HLT", "RET", "FCLR", "VFCLR", "VWAIT"})

_RE_PAGE_DIRECTIVE = re.compile(r"^\s*@page\b", re.IGNORECASE)
_RE_PAGE_FULL = re.compile(r"^\s*@page\s+(\S+)(?:\s*,\s*(\S+))?\s*$", re.IGNORECASE)
_RE_PAGE_BARE = re.compile(r"^\s*@page\s*$", re.IGNORECASE)
_RE_LABEL_DEF = re.compile(r"^([.A-Za-z]\w*)\s*:")
_RE_LABEL_START = re.compile(r"^[.A-Za-z]\w*\s*:")


def _parse_page_directive(text: str, line_no: int) -> ParsedLine | None:
    """Parse @page directive. Returns ParsedLine or None if not a directive."""
    if not _RE_PAGE_DIRECTIVE.match(text):
        return None
    if _RE_LABEL_START.match(text):
        raise ParseError("@page must be on its own line", line_no)
    m = _RE_PAGE_FULL.match(text)
    if not m:
        if _RE_PAGE_BARE.match(text):
            raise ParseError("@page: missing page number", line_no)
        raise ParseError("@page: invalid syntax", line_no)
    page_val = _try_parse_number(m.group(1))
    if page_val is None:
        raise ParseError("@page: invalid syntax", line_no)
    if page_val < 0 or page_val > 255:
        raise ParseError("@page value must be 0-255", line_no)
    operands: list[Operand] = [OpConst(page_val)]
    if m.group(2) is not None:
        offset_val = _try_parse_number(m.group(2))
        if offset_val is None:
            raise ParseError("@page: invalid offset", line_no)
        if offset_val < 0 or offset_val > 255:
            raise ParseError("@page offset must be 0-255", line_no)
        operands.append(OpConst(offset_val))
    return ParsedLine(line_no=line_no, mnemonic="@PAGE", operands=operands)


def _parse_label(text: str, line_no: int, arch: int) -> tuple[str | None, str]:
    """Extract label from start of text. Returns (label, remaining_text)."""
    label_match = _RE_LABEL_DEF.match(text)
    if not label_match:
        return None, text
    label_name = label_match.group(1)
    up = label_name.upper()
    if up in REGISTERS or (arch >= 2 and up in FORBIDDEN_FP_LABEL_NAMES):
        raise ParseError(f"Label contains keyword: {up}", line_no)
    return label_name.lower(), text[label_match.end() :].strip()


def _validate_fp_suffixes(mnemonic: str, dst_suffix: str | None, src_suffix: str | None, line_no: int) -> None:
    """Validate that FP format suffixes are present/absent as required."""
    if mnemonic in FP_CONTROL_MNEMONICS:
        if dst_suffix is not None:
            raise ParseError("Syntax error", line_no)
    elif mnemonic == "FCVT":
        if dst_suffix is None or src_suffix is None:
            raise ParseError("FP format suffix required", line_no)
    elif dst_suffix is None:
        raise ParseError("FP format suffix required", line_no)


def _resolve_mnemonic(mnemonic_raw: str, line_no: int, arch: int) -> tuple[str, str | None, str | None]:
    """Resolve mnemonic, aliases, and FP suffixes.

    Returns (mnemonic, dst_suffix, src_suffix).
    """
    mnemonic = MNEMONIC_ALIASES.get(mnemonic_raw, mnemonic_raw)
    dst_suffix: str | None = None
    src_suffix: str | None = None

    _dotted = (MNEMONICS_FP if arch >= 2 else frozenset()) | (MNEMONICS_VU if arch >= 3 else frozenset())
    if "." in mnemonic and _dotted:
        dot_parts = mnemonic.split(".")
        base = dot_parts[0]
        if base in _dotted:
            if len(dot_parts) > 3:
                raise ParseError("Syntax error", line_no)
            mnemonic = base
            dst_suffix = dot_parts[1] if len(dot_parts) > 1 else None
            src_suffix = dot_parts[2] if len(dot_parts) > 2 else None

    all_mnemonics = (
        MNEMONICS | (MNEMONICS_FP if arch >= 2 else frozenset()) | (MNEMONICS_VU if arch >= 3 else frozenset())
    )
    if mnemonic not in all_mnemonics:
        if _RE_LABEL.match(mnemonic_raw):
            raise ParseError(f"Invalid instruction: {mnemonic_raw}", line_no)
        raise ParseError("Syntax error", line_no)

    if arch >= 2 and mnemonic in MNEMONICS_FP:
        _validate_fp_suffixes(mnemonic, dst_suffix, src_suffix, line_no)

    return mnemonic, dst_suffix, src_suffix


def parse_line(raw: str, line_no: int, arch: int = 1) -> ParsedLine:
    """Parse a single source line."""
    text = _tokenize_line(raw)
    if not text:
        return ParsedLine(line_no=line_no)

    page_result = _parse_page_directive(text, line_no)
    if page_result is not None:
        return page_result

    label, text = _parse_label(text, line_no, arch)
    if not text:
        return ParsedLine(line_no=line_no, label=label)

    parts = text.split(None, 1)
    mnemonic, dst_suffix, src_suffix = _resolve_mnemonic(parts[0].upper(), line_no, arch)
    operand_str = parts[1].strip() if len(parts) > 1 else ""

    if mnemonic == "DB":
        operands = _parse_db_operands(operand_str, line_no, arch=arch)
    elif mnemonic in _ZERO_ARG_MNEMONICS:
        if operand_str:
            raise ParseError(f"{mnemonic}: too many arguments", line_no)
        operands = []
    else:
        operands = [_parse_operand(t, line_no, arch) for t in _split_operands(operand_str)]

    return ParsedLine(
        line_no=line_no,
        label=label,
        mnemonic=mnemonic,
        operands=operands,
        dst_suffix=dst_suffix,
        src_suffix=src_suffix,
    )


def parse_lines(source: str, arch: int = 1) -> list[ParsedLine]:
    """Parse all lines from source text."""
    lines = source.split("\n")
    parsed: list[ParsedLine] = []
    labels_seen: dict[str, int] = {}

    for i, raw in enumerate(lines, start=1):
        p = parse_line(raw, i, arch=arch)

        if p.label is not None:
            if p.label in labels_seen:
                raise ParseError(f"Duplicate label: {p.label}", i)
            labels_seen[p.label] = i

        parsed.append(p)

    return parsed
