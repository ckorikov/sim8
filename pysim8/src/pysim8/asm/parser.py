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
    REGISTERS, MNEMONIC_ALIASES, MNEMONICS,
    FP_REGISTERS, MNEMONICS_FP, FP_CONTROL_MNEMONICS,
)

__all__ = [
    "ParsedLine",
    "OpReg",
    "OpConst",
    "OpAddr",
    "OpRegAddr",
    "OpString",
    "OpLabel",
    "OpFpReg",
    "OpFloat",
    "parse_lines",
    "AsmError",
    "ParseError",
]


# ── Exceptions ─────────────────────────────────────────────────────


class AsmError(Exception):
    """Base error for all assembly-related errors."""

    def __init__(self, message: str, line: int) -> None:
        self.message = message
        self.line = line
        super().__init__(f"Line {line}: {message}")


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
class OpFpReg:
    """FP register operand: FA, FHA, FHB, FQA-FQD, FOA-FOH."""

    name: str    # uppercase: "FA", "FHA", etc.
    pos: int     # position within format (0-7)
    fmt: int     # canonical format code
    width: int   # register width in bits


@dataclass(frozen=True, slots=True)
class OpFloat:
    """Float literal for DB directive."""

    value: float
    fmt: int  # FP_FMT_* constant


Operand = (
    OpReg | OpConst | OpAddr | OpRegAddr | OpString | OpLabel
    | OpFpReg | OpFloat
)


# ── Parsed line ─────────────────────────────────────────────────────


@dataclass(slots=True)
class ParsedLine:
    """Result of parsing one source line."""

    line_no: int
    label: str | None = None
    mnemonic: str | None = None
    operands: list[Operand] | None = None
    dst_suffix: str | None = None   # destination format suffix e.g. "F", "H", "BF"
    src_suffix: str | None = None   # source format suffix for FCVT.dst.src


# ── Number parsing ──────────────────────────────────────────────────

# Regex patterns for number formats
_RE_HEX = re.compile(r"^0x([0-9A-Fa-f]+)$")
_RE_OCT = re.compile(r"^0o([0-7]+)$")
_RE_BIN = re.compile(r"^([01]+)b$")
_RE_DEC_EXPLICIT = re.compile(r"^(\d+)d$")
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
    (_RE_DEC, 10),
)


def _try_parse_number(token: str) -> int | None:
    """Try to parse a numeric literal. Returns value or None."""
    if m := _RE_CHAR_MULTI.match(token):
        return None  # multi-char literals handled as error elsewhere
    if m := _RE_CHAR.match(token):
        return ord(m.group(1))
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
    """Validate value is in 0-255."""
    if value < 0 or value > 255:
        raise ParseError(
            f"{value} must have a value between 0-255", line
        )
    return value


# ── Bracket operand parsing ─────────────────────────────────────────

_RE_BRACKET = re.compile(r"^\[(.+)\]$")
_RE_REG_OFFSET = re.compile(
    r"^([A-Za-z]+)\s*([+-])\s*(\d+)$"
)
_RE_REG_ONLY = re.compile(r"^([A-Za-z]+)$")


def _parse_bracket_operand(inner: str, line: int) -> OpAddr | OpRegAddr:
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
            raise ParseError(
                f"Invalid register in address: {m.group(1)}", line
            )
        if offset_val < -16 or offset_val > 15:
            raise ParseError(
                "offset must be a value between -16...+15", line
            )
        return OpRegAddr(REGISTERS[reg_name], offset_val)

    # [reg]
    if m := _RE_REG_ONLY.match(inner):
        reg_name = m.group(1).upper()
        if reg_name in REGISTERS:
            return OpRegAddr(REGISTERS[reg_name], 0)

    # [number] → direct address
    val = _try_parse_number(inner)
    if val is None:
        raise ParseError(f"Invalid address: {inner}", line)
    _check_byte_range(val, line)
    return OpAddr(val)


# ── Operand parsing ─────────────────────────────────────────────────


def _try_bracket(token: str, line: int) -> Operand | None:
    """Try to parse bracket operand: [addr], [reg], [reg±offset]."""
    if m := _RE_BRACKET.match(token):
        return _parse_bracket_operand(m.group(1), line)
    return None


def _try_register(token: str, line: int) -> Operand | None:
    """Try to parse register name: A, B, C, D, SP, DP, or FP regs."""
    up = token.upper()
    if up in REGISTERS:
        return OpReg(REGISTERS[up])
    if up in FP_REGISTERS:
        pos, fmt, width = FP_REGISTERS[up]
        return OpFpReg(up, pos, fmt, width)
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


def _try_label(token: str, line: int) -> Operand | None:
    """Try to parse label reference (identifier not matching above)."""
    if _RE_LABEL.match(token):
        return OpLabel(token.lower())
    return None


# Order matters: bracket is unambiguous ('['), register is a finite set,
# string is unambiguous ('"'), number has specific formats,
# label is the fallback for any remaining identifier.
_OPERAND_PARSERS = [
    _try_bracket,
    _try_register,
    _try_string,
    _try_const,
    _try_label,
]


def _parse_operand(token: str, line: int) -> Operand:
    """Parse a single operand token into an Operand."""
    token = token.strip()
    for parser in _OPERAND_PARSERS:
        result = parser(token, line)
        if result is not None:
            return result
    raise ParseError(f"Invalid operand: {token}", line)


# ── Float literal parsing ──────────────────────────────────────────

_RE_FLOAT = re.compile(
    r'^([+-]?)(\d+\.\d*|\.\d+)([eE][+-]?\d+)?(_\w+)?$'
)
_RE_FLOAT_SPECIAL = re.compile(
    r'^([+-]?)(inf|nan)(_\w+)?$', re.IGNORECASE
)


def _resolve_db_float_suffix(
    suffix_str: str | None, line: int
) -> int:
    """Resolve DB float suffix to format code. Default is float32."""
    from pysim8.isa import FP_DB_SUFFIX_TO_FMT, FP_FMT_F, FP_FMT_N1, FP_FMT_N2
    if suffix_str is None:
        return FP_FMT_F  # default float32
    suffix = suffix_str[1:].upper()  # strip leading _
    if suffix not in FP_DB_SUFFIX_TO_FMT:
        raise ParseError("Invalid float literal", line)
    fmt = FP_DB_SUFFIX_TO_FMT[suffix]
    if fmt in (FP_FMT_N1, FP_FMT_N2):
        raise ParseError(
            f"Unsupported float format for DB: {suffix_str[1:]}", line
        )
    return fmt


def _parse_float_literal(
    token: str, line: int
) -> OpFloat | None:
    """Try to parse a float literal: 1.4, 1.4_h, inf_f, nan_h."""
    # Try special values first
    m = _RE_FLOAT_SPECIAL.match(token)
    if m:
        sign_str = m.group(1)
        name = m.group(2)
        suffix_str = m.group(3)
        fmt = _resolve_db_float_suffix(suffix_str, line)
        if name.lower() == "inf":
            val = float("-inf") if sign_str == "-" else float("inf")
        else:
            val = float("nan")
            if sign_str == "-":
                val = -val
        return OpFloat(val, fmt)

    # Try numeric float
    m = _RE_FLOAT.match(token)
    if m:
        sign_str = m.group(1)
        num = m.group(2)
        exp = m.group(3)
        suffix_str = m.group(4)
        fmt = _resolve_db_float_suffix(suffix_str, line)
        text = (sign_str or "") + num + (exp or "")
        try:
            val = float(text)
        except ValueError:
            raise ParseError("Invalid float literal", line)
        return OpFloat(val, fmt)

    return None


# ── DB operand parsing ──────────────────────────────────────────────


def _parse_db_operands(
    raw: str, line: int, arch: int = 1
) -> list[Operand]:
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
                        "DB does not support mixing float and"
                        " integer operands",
                        line,
                    )
                has_float = True
                operands.append(fp)
                continue

        # Integer value
        if has_float:
            raise ParseError(
                "DB does not support mixing float and"
                " integer operands",
                line,
            )

        if _RE_LABEL.match(part) and _try_parse_number(part) is None:
            # Reject labels and float specials when not parsed above
            lower = part.lower()
            if lower in ("inf", "nan") or lower.startswith((
                "inf_", "nan_", "-inf", "-nan",
            )):
                raise ParseError(
                    "DB does not support this operand", line
                )
            raise ParseError(
                "DB does not support this operand", line
            )

        has_int = True
        val = parse_number(part, line)
        _check_byte_range(val, line)
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
                result.append(line[i:i + 3])
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


def parse_line(
    raw: str, line_no: int, arch: int = 1
) -> ParsedLine:
    """Parse a single source line."""
    text = _tokenize_line(raw)

    result = ParsedLine(line_no=line_no)

    if not text:
        return result

    # Check for label
    label_match = re.match(r"^([.A-Za-z]\w*)\s*:", text)
    if label_match:
        label_name = label_match.group(1)
        # Validate label
        if label_name.upper() in REGISTERS:
            raise ParseError(
                f"Label contains keyword: {label_name.upper()}",
                line_no,
            )
        if arch >= 2 and label_name.upper() in FP_REGISTERS:
            raise ParseError(
                f"Label contains keyword: {label_name.upper()}",
                line_no,
            )
        result.label = label_name.lower()
        text = text[label_match.end():].strip()

    if not text:
        return result

    # Split mnemonic from operands
    parts = text.split(None, 1)
    mnemonic_raw = parts[0].upper()

    # Resolve aliases
    mnemonic = MNEMONIC_ALIASES.get(mnemonic_raw, mnemonic_raw)

    # Check for FP mnemonic with suffix (contains dot)
    dst_suffix: str | None = None
    src_suffix: str | None = None
    if "." in mnemonic and arch >= 2:
        dot_parts = mnemonic.split(".")
        base = dot_parts[0]
        if base in MNEMONICS_FP:
            mnemonic = base
            dst_suffix = dot_parts[1] if len(dot_parts) > 1 else None
            src_suffix = dot_parts[2] if len(dot_parts) > 2 else None
            if len(dot_parts) > 3:
                raise ParseError("Syntax error", line_no)

    # Check against known mnemonics
    all_mnemonics = (
        MNEMONICS if arch < 2 else MNEMONICS | MNEMONICS_FP
    )
    if mnemonic not in all_mnemonics:
        if _RE_LABEL.match(mnemonic_raw):
            raise ParseError(
                f"Invalid instruction: {mnemonic_raw}", line_no
            )
        raise ParseError("Syntax error", line_no)

    # Validate FP suffix requirements
    if arch >= 2 and mnemonic in MNEMONICS_FP:
        if mnemonic in FP_CONTROL_MNEMONICS:
            if dst_suffix is not None:
                raise ParseError("Syntax error", line_no)
        elif mnemonic == "FCVT":
            if dst_suffix is None or src_suffix is None:
                raise ParseError(
                    "FP format suffix required", line_no
                )
        else:
            if dst_suffix is None:
                raise ParseError(
                    "FP format suffix required", line_no
                )

    result.mnemonic = mnemonic
    result.dst_suffix = dst_suffix
    result.src_suffix = src_suffix
    operand_str = parts[1].strip() if len(parts) > 1 else ""

    # Parse operands based on mnemonic
    if mnemonic == "DB":
        result.operands = _parse_db_operands(
            operand_str, line_no, arch=arch
        )
        return result

    if mnemonic in ("HLT", "RET", "FCLR"):
        if operand_str:
            raise ParseError(
                f"{mnemonic}: too many arguments", line_no
            )
        result.operands = []
        return result

    # Split and parse operands
    if operand_str:
        tokens = _split_operands(operand_str)
        result.operands = [
            _parse_operand(t, line_no) for t in tokens
        ]
    else:
        result.operands = []

    return result


def parse_lines(
    source: str, arch: int = 1
) -> list[ParsedLine]:
    """Parse all lines from source text."""
    lines = source.split("\n")
    parsed: list[ParsedLine] = []
    labels_seen: dict[str, int] = {}

    for i, raw in enumerate(lines, start=1):
        p = parse_line(raw, i, arch=arch)

        # Check for duplicate labels
        if p.label is not None:
            if p.label in labels_seen:
                raise ParseError(f"Duplicate label: {p.label}", i)
            labels_seen[p.label] = i

        parsed.append(p)

    return parsed
