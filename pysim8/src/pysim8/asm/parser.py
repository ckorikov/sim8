"""Tokenizer and parser for assembly source.

Parses each source line into a structured representation:
  - label (optional)
  - instruction mnemonic
  - typed operands (Reg, Const, Addr, RegAddr, String, FpReg, Float)
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from pysim8.isa import (
    FORBIDDEN_FP_LABEL_NAMES,
    FP_CONTROL_MNEMONICS,
    FP_FMT_F,
    FP_FMT_N1,
    FP_FMT_N2,
    FP_REGISTERS,
    FP_SUFFIX_TO_FMT,
    MNEMONIC_ALIASES,
    MNEMONICS,
    MNEMONICS_FP,
    MNEMONICS_VU,
    REGISTERS,
    VU_REGISTERS,
)

__all__ = [
    "ParsedLine",
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
]


# ── Exceptions ─────────────────────────────────────────────────────


class AsmError(Exception):
    """Base error for all assembly-related errors."""

    def __init__(self, message: str, line: int, filename: str | None = None) -> None:
        self.message = message
        self.line = line
        self.filename = filename
        loc = f"{filename}:{line}" if filename else f"line {line}"
        super().__init__(f"{loc}: {message}")


class ParseError(AsmError):
    """Raised for syntax/parse errors."""


# ── Operand types ───────────────────────────────────────────────────


@dataclass(frozen=True, slots=True)
class OpReg:
    """Register operand: A, B, C, D, SP, DP."""

    code: int


@dataclass(frozen=True, slots=True)
class OpConst:
    """Immediate constant (0-255)."""

    value: int


@dataclass(frozen=True, slots=True)
class OpAddr:
    """Direct memory address: [const]."""

    value: int


@dataclass(frozen=True, slots=True)
class OpRegAddr:
    """Register indirect with optional offset: [reg±offset]."""

    reg_code: int
    offset: int  # -16..+15


@dataclass(frozen=True, slots=True)
class OpString:
    """String literal for DB."""

    text: str


@dataclass(frozen=True, slots=True)
class OpLabel:
    """Unresolved label reference (to be resolved in pass 2)."""

    name: str


@dataclass(frozen=True, slots=True)
class OpAddrLabel:
    """Unresolved label inside brackets: [label] → direct address in pass 2."""

    name: str


@dataclass(frozen=True, slots=True)
class OpPageLabel:
    """Page number of label: {label} → resolves to label's page in pass 2."""

    name: str


@dataclass(frozen=True, slots=True)
class OpFpReg:
    """FP register operand: FA/FB, FHA-FHD, FQA-FQH, FOA-FOP."""

    name: str  # uppercase: "FA", "FHA", "FB", etc.
    pos: int  # position within format (0-7)
    fmt: int  # canonical format code
    phys: int  # physical register index (0 or 1)


@dataclass(frozen=True, slots=True)
class OpFloat:
    """Float literal for DB directive."""

    value: float
    fmt: int  # FP_FMT_* constant


@dataclass(frozen=True, slots=True)
class OpFpImm:
    """FP immediate literal for FMOV instruction."""

    value: float
    fmt: int | None  # FP_FMT_* or None (resolved from instruction suffix)


@dataclass(frozen=True, slots=True)
class OpVuReg:
    """VU register operand: VA, VB, VC, VM, VL."""

    code: int  # 0=VA, 1=VB, 2=VC, 3=VM, 4=VL


Operand = (
    OpReg
    | OpConst
    | OpAddr
    | OpRegAddr
    | OpString
    | OpLabel
    | OpAddrLabel
    | OpPageLabel
    | OpFpReg
    | OpFloat
    | OpFpImm
    | OpVuReg
)


# ── Parsed line ─────────────────────────────────────────────────────


@dataclass(slots=True)
class ParsedLine:
    """Result of parsing one source line."""

    line_no: int
    label: str | None = None
    mnemonic: str | None = None
    operands: list[Operand] | None = None
    dst_suffix: str | None = None  # destination format suffix e.g. "F", "H", "BF"
    src_suffix: str | None = None  # source format suffix for FCVT.dst.src


# ── Number parsing ──────────────────────────────────────────────────

# Regex patterns for number formats
_RE_HEX = re.compile(r"^0x([0-9A-Fa-f]+)$")
_RE_OCT = re.compile(r"^0o([0-7]+)$")
_RE_BIN = re.compile(r"^([01]+)b$")
_RE_DEC_EXPLICIT = re.compile(r"^(\d+)d$")
_RE_DEC_UNSIGNED = re.compile(r"^(\d+)u$")  # C-style unsigned suffix
_RE_DEC = re.compile(r"^(\d+)$")
_RE_CHAR = re.compile(r"^'(.)'$")
_RE_CHAR_MULTI = re.compile(r"^'(.{2,})'$")

# Label pattern
_RE_LABEL = re.compile(r"^[.A-Za-z]\w*$")

# Number format table: (regex, base) — regex already validated charset,
# so int() cannot raise ValueError.
_NUM_FORMATS: tuple[tuple[re.Pattern[str], int], ...] = (
    (_RE_HEX, 16),
    (_RE_OCT, 8),
    (_RE_BIN, 2),
    (_RE_DEC_EXPLICIT, 10),
    (_RE_DEC_UNSIGNED, 10),
    (_RE_DEC, 10),
)


def _try_parse_number(token: str) -> int | None:
    """Try to parse a numeric literal. Returns value or None.

    Supports negative decimals: -5, -128. Stored as two's complement by caller.
    """
    if m := _RE_CHAR_MULTI.match(token):
        return None  # multi-char literals handled as error elsewhere
    if m := _RE_CHAR.match(token):
        return ord(m.group(1))
    # Handle negative prefix (decimal only)
    if token.startswith("-"):
        inner = token[1:]
        for pattern, base in _NUM_FORMATS:
            if base == 10 and (m := pattern.match(inner)):
                return -int(m.group(1), base)
        return None
    for pattern, base in _NUM_FORMATS:
        if m := pattern.match(token):
            return int(m.group(1), base)
    return None


def parse_number(token: str, line: int) -> int:
    """Parse a numeric literal. Returns integer value. Raises on invalid."""
    if _RE_CHAR_MULTI.match(token):
        raise ParseError("Only one character is allowed", line)
    val = _try_parse_number(token)
    if val is None:
        raise ParseError("Invalid number format", line)
    return val


def _check_byte_range(value: int, line: int) -> int:
    """Validate value is in -128..255 and convert negatives to two's complement."""
    if value < -128 or value > 255:
        raise ParseError(f"{value} must have a value between -128 and 255", line)
    return value & 0xFF


# ── Bracket operand parsing ─────────────────────────────────────────

_RE_BRACKET = re.compile(r"^\[(.+)\]$")
_RE_REG_OFFSET = re.compile(r"^([A-Za-z]+)\s*([+-])\s*(\d+)$")
_RE_REG_ONLY = re.compile(r"^([A-Za-z]+)$")


def _parse_bracket_operand(inner: str, line: int) -> OpAddr | OpRegAddr | OpAddrLabel:
    """Parse content inside brackets: [addr], [reg], [reg±offset]."""
    inner = inner.strip()

    # [reg±offset]
    if m := _RE_REG_OFFSET.match(inner):
        reg_name = m.group(1).upper()
        sign = m.group(2)
        offset_val = int(m.group(3))
        if sign == "-":
            offset_val = -offset_val
        if reg_name not in REGISTERS:
            raise ParseError(f"Invalid register in address: {m.group(1)}", line)
        if offset_val < -16 or offset_val > 15:
            raise ParseError("offset must be a value between -16...+15", line)
        return OpRegAddr(REGISTERS[reg_name], offset_val)

    # [reg]
    if m := _RE_REG_ONLY.match(inner):
        reg_name = m.group(1).upper()
        if reg_name in REGISTERS:
            return OpRegAddr(REGISTERS[reg_name], 0)

    # [number] → direct address
    val = _try_parse_number(inner)
    if val is not None:
        _check_byte_range(val, line)
        return OpAddr(val)

    # [label] → direct address resolved in pass 2
    if _RE_LABEL.match(inner):
        return OpAddrLabel(inner.lower())

    raise ParseError(f"Invalid address: {inner}", line)


# ── Operand parsing ─────────────────────────────────────────────────


def _try_bracket(token: str, line: int) -> Operand | None:
    """Try to parse bracket operand: [addr], [reg], [reg±offset]."""
    if m := _RE_BRACKET.match(token):
        return _parse_bracket_operand(m.group(1), line)
    return None


def _try_register(token: str, line: int, arch: int = 1) -> Operand | None:
    """Try to parse register name: A, B, C, D, SP, DP, FP regs, or VU regs."""
    up = token.upper()
    if up in REGISTERS:
        return OpReg(REGISTERS[up])
    if arch >= 3 and up in VU_REGISTERS:
        return OpVuReg(VU_REGISTERS[up])
    if up in FP_REGISTERS:
        info = FP_REGISTERS[up]
        return OpFpReg(up, info.pos, info.fmt, info.phys)
    return None


def _try_string(token: str, line: int) -> Operand | None:
    """Try to parse string literal: "..."."""
    if token.startswith('"') and token.endswith('"'):
        return OpString(token[1:-1])
    return None


def _try_const(token: str, line: int) -> Operand | None:
    """Try to parse numeric constant or char literal."""
    if _RE_CHAR_MULTI.match(token):
        raise ParseError("Only one character is allowed", line)
    val = _try_parse_number(token)
    if val is not None:
        _check_byte_range(val, line)
        return OpConst(val)
    return None


_RE_FLOAT = re.compile(r"^([+-]?)(\d+\.\d*|\.\d+)([eE][+-]?\d+)?(_\w+)?$")
_RE_FLOAT_SPECIAL = re.compile(r"^([+-]?)(inf|nan)(_\w+)?$", re.IGNORECASE)


def _match_float_token(token: str, line: int) -> tuple[float, str | None] | None:
    """Match a float token → (value, suffix_str), or None if not a float."""
    m = _RE_FLOAT_SPECIAL.match(token)
    if m:
        sign_str, name, suffix_str = m.group(1), m.group(2), m.group(3)
        if name.lower() == "inf":
            val = float("-inf") if sign_str == "-" else float("inf")
        else:
            val = float("nan")
            if sign_str == "-":
                val = -val
        return val, suffix_str

    m = _RE_FLOAT.match(token)
    if m:
        sign_str, num, exp, suffix_str = m.group(1), m.group(2), m.group(3), m.group(4)
        try:
            val = float((sign_str or "") + num + (exp or ""))
        except ValueError:
            raise ParseError("Invalid float literal", line)
        return val, suffix_str

    return None


def _resolve_fp_imm_suffix(suffix_str: str | None, line: int) -> int | None:
    """Resolve FP immediate literal suffix to fmt code (None if no suffix)."""
    if suffix_str is None:
        return None
    suffix = suffix_str[1:].upper()
    if suffix not in FP_SUFFIX_TO_FMT:
        raise ParseError("Invalid float literal", line)
    return FP_SUFFIX_TO_FMT[suffix]


def _try_fp_imm(token: str, line: int) -> Operand | None:
    result = _match_float_token(token, line)
    if result is None:
        return None
    val, suffix_str = result
    return OpFpImm(val, _resolve_fp_imm_suffix(suffix_str, line))


_RE_PAGE_LABEL = re.compile(r"^\{(.+)\}$")


def _try_page_label(token: str, line: int) -> Operand | None:
    """Try to parse {label} → page number of label."""
    m = _RE_PAGE_LABEL.match(token)
    if not m:
        return None
    inner = m.group(1).strip()
    if not inner:
        raise ParseError("Syntax error", line)
    if not _RE_LABEL.match(inner):
        raise ParseError("Syntax error", line)
    return OpPageLabel(inner.lower())


def _try_label(token: str, line: int) -> Operand | None:
    """Try to parse label reference (identifier not matching above)."""
    if _RE_LABEL.match(token):
        return OpLabel(token.lower())
    return None


# Order matters: bracket is unambiguous ('['), page label is unambiguous ('{'),
# register is a finite set, string is unambiguous ('"'), number has specific formats,
# FP imm catches float literals (must come before label to grab inf/nan),
# label is the fallback for any remaining identifier.
_OPERAND_PARSERS = [
    _try_bracket,
    _try_page_label,
    _try_register,
    _try_string,
    _try_const,
    _try_fp_imm,
    _try_label,
]


def _parse_operand(token: str, line: int, arch: int = 1) -> Operand:
    """Parse a single operand token into an Operand."""
    token = token.strip()
    # arch >= 3: try 16-bit number first (for VSET etc — codegen validates range)
    if arch >= 3:
        val = _try_parse_number(token)
        if val is not None and val > 255:
            return OpConst(val)
    for parser in _OPERAND_PARSERS:
        if parser is _try_register:
            result = _try_register(token, line, arch)
        else:
            result = parser(token, line)
        if result is not None:
            return result
    raise ParseError(f"Invalid operand: {token}", line)


# ── Float literal parsing ──────────────────────────────────────────


def _resolve_db_float_suffix(suffix_str: str | None, line: int) -> int:
    """Resolve DB float suffix to format code. Default is float32."""
    if suffix_str is None:
        return FP_FMT_F
    suffix = suffix_str[1:].upper()
    if suffix not in FP_SUFFIX_TO_FMT:
        raise ParseError("Invalid float literal", line)
    fmt = FP_SUFFIX_TO_FMT[suffix]
    if fmt in (FP_FMT_N1, FP_FMT_N2):
        raise ParseError(f"Unsupported float format for DB: {suffix_str[1:]}", line)
    return fmt


def _parse_float_literal(token: str, line: int) -> OpFloat | None:
    result = _match_float_token(token, line)
    if result is None:
        return None
    val, suffix_str = result
    return OpFloat(val, _resolve_db_float_suffix(suffix_str, line))


# ── DB operand parsing ──────────────────────────────────────────────


def _parse_db_operands(raw: str, line: int, arch: int = 1) -> list[Operand]:
    """Parse DB operands: const, comma-list, string, or float."""
    raw = raw.strip()

    # String literal
    if raw.startswith('"') and raw.endswith('"'):
        return [OpString(raw[1:-1])]

    # Comma-separated list of values
    parts = [p.strip() for p in raw.split(",")]
    operands: list[Operand] = []
    has_float = False
    has_int = False

    for part in parts:
        if not part:
            continue
        if part.startswith("["):
            raise ParseError("DB does not support this operand", line)
        up = part.upper()
        if up in REGISTERS:
            raise ParseError("DB does not support this operand", line)

        # Try float literal first (if arch >= 2)
        if arch >= 2:
            fp = _parse_float_literal(part, line)
            if fp is not None:
                if has_int:
                    raise ParseError(
                        "DB does not support mixing float and integer operands",
                        line,
                    )
                has_float = True
                operands.append(fp)
                continue

        # Integer value
        if has_float:
            raise ParseError(
                "DB does not support mixing float and integer operands",
                line,
            )

        if _RE_LABEL.match(part) and _try_parse_number(part) is None:
            raise ParseError("DB does not support this operand", line)

        has_int = True
        val = parse_number(part, line)
        val = _check_byte_range(val, line)
        operands.append(OpConst(val))
    return operands


# ── Line parsing ────────────────────────────────────────────────────


def _tokenize_line(line: str) -> str:
    """Strip comments and whitespace from a line."""
    result: list[str] = []
    in_string = False
    i = 0
    while i < len(line):
        ch = line[i]
        if ch == '"':
            in_string = not in_string
        elif ch == "'" and not in_string:
            # Consume char literal as a unit: 'X'
            if i + 2 < len(line) and line[i + 2] == "'":
                result.append(line[i : i + 3])
                i += 3
                continue
        elif ch == ";" and not in_string:
            break
        result.append(ch)
        i += 1
    return "".join(result).strip()


def _split_operands(operand_str: str) -> list[str]:
    """Split operand string by commas, respecting brackets and strings."""
    parts: list[str] = []
    current: list[str] = []
    depth = 0
    in_string = False

    for ch in operand_str:
        if ch == '"':
            in_string = not in_string
        elif ch == "[" and not in_string:
            depth += 1
        elif ch == "]" and not in_string:
            depth -= 1
        elif ch == "," and depth == 0 and not in_string:
            parts.append("".join(current).strip())
            current = []
            continue
        current.append(ch)

    if current:
        parts.append("".join(current).strip())
    return [p for p in parts if p]


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


def _resolve_mnemonic(mnemonic_raw: str, line_no: int, arch: int) -> tuple[str, str | None, str | None]:
    """Resolve mnemonic, aliases, and FP suffixes.

    Returns (mnemonic, dst_suffix, src_suffix).
    """
    mnemonic = MNEMONIC_ALIASES.get(mnemonic_raw, mnemonic_raw)
    dst_suffix: str | None = None
    src_suffix: str | None = None

    _dotted = MNEMONICS_FP if arch >= 2 else frozenset()
    if arch >= 3:
        _dotted = _dotted | MNEMONICS_VU
    if "." in mnemonic and _dotted:
        dot_parts = mnemonic.split(".")
        base = dot_parts[0]
        if base in _dotted:
            if len(dot_parts) > 3:
                raise ParseError("Syntax error", line_no)
            mnemonic = base
            dst_suffix = dot_parts[1] if len(dot_parts) > 1 else None
            src_suffix = dot_parts[2] if len(dot_parts) > 2 else None

    all_mnemonics = MNEMONICS if arch < 2 else MNEMONICS | MNEMONICS_FP
    if arch >= 3:
        all_mnemonics = all_mnemonics | MNEMONICS_VU
    if mnemonic not in all_mnemonics:
        if _RE_LABEL.match(mnemonic_raw):
            raise ParseError(f"Invalid instruction: {mnemonic_raw}", line_no)
        raise ParseError("Syntax error", line_no)

    if arch >= 2 and mnemonic in MNEMONICS_FP:
        if mnemonic in FP_CONTROL_MNEMONICS:
            if dst_suffix is not None:
                raise ParseError("Syntax error", line_no)
        elif mnemonic == "FCVT":
            if dst_suffix is None or src_suffix is None:
                raise ParseError("FP format suffix required", line_no)
        else:
            if dst_suffix is None:
                raise ParseError("FP format suffix required", line_no)

    return mnemonic, dst_suffix, src_suffix


def parse_line(raw: str, line_no: int, arch: int = 1) -> ParsedLine:
    """Parse a single source line."""
    text = _tokenize_line(raw)
    if not text:
        return ParsedLine(line_no=line_no)

    # @page directive (must come before label check)
    page_result = _parse_page_directive(text, line_no)
    if page_result is not None:
        return page_result

    # Label and remaining text
    label, text = _parse_label(text, line_no, arch)
    if not text:
        return ParsedLine(line_no=line_no, label=label)

    # Mnemonic and FP suffixes
    parts = text.split(None, 1)
    mnemonic, dst_suffix, src_suffix = _resolve_mnemonic(parts[0].upper(), line_no, arch)
    operand_str = parts[1].strip() if len(parts) > 1 else ""

    # Parse operands
    if mnemonic == "DB":
        operands = _parse_db_operands(operand_str, line_no, arch=arch)
    elif mnemonic in ("HLT", "RET", "FCLR", "VFCLR", "VWAIT"):
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
