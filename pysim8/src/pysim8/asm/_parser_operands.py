"""Operand-level parsing: number parsers, bracket/operand parsers, tokenizer."""

from __future__ import annotations

import re
from collections.abc import Callable

from pysim8.asm._parser_types import (
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
    ParseError,
)
from pysim8.isa import (
    FP_FMT_F,
    FP_FMT_N1,
    FP_FMT_N2,
    FP_REGISTERS,
    FP_SUFFIX_TO_FMT,
    REGISTERS,
    VU_REGISTERS,
)

# ── Number parsing ──────────────────────────────────────────────────

_RE_HEX = re.compile(r"^0x([0-9A-Fa-f]+)$")
_RE_OCT = re.compile(r"^0o([0-7]+)$")
_RE_BIN = re.compile(r"^([01]+)b$")
_RE_DEC_EXPLICIT = re.compile(r"^(\d+)d$")
_RE_DEC_UNSIGNED = re.compile(r"^(\d+)u$")
_RE_DEC = re.compile(r"^(\d+)$")
_RE_CHAR = re.compile(r"^'(.)'$")
_RE_CHAR_MULTI = re.compile(r"^'(.{2,})'$")

# Label pattern
_RE_LABEL = re.compile(r"^[.A-Za-z]\w*$")

# Number format table: (regex, base)
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


def _validate_byte_range(value: int, line: int) -> int:
    """Validate value is in -128..255 and convert negatives to two's complement."""
    if value < -128 or value > 255:
        raise ParseError(f"{value} must have a value between -128 and 255", line)
    return value & 0xFF


# ── Bracket operand parsing ─────────────────────────────────────────

_RE_BRACKET = re.compile(r"^\[(.+)\]$")
_RE_REG_OFFSET = re.compile(r"^([A-Za-z]+)\s*([+-])\s*(\d+)$")
_RE_REG_ONLY = re.compile(r"^([A-Za-z]+)$")


_RE_LABEL_OFFSET = re.compile(r"^([.A-Za-z]\w*)\s*([+-])\s*(\d+)$")


def _parse_bracket_operand(inner: str, line: int) -> OpAddr | OpRegAddr | OpAddrLabel:
    """Parse content inside brackets: [addr], [reg], [reg±offset], [label±N]."""
    inner = inner.strip()

    if m := _RE_REG_OFFSET.match(inner):
        reg_name = m.group(1).upper()
        sign = m.group(2)
        offset_val = int(m.group(3))
        if sign == "-":
            offset_val = -offset_val
        if reg_name in REGISTERS:
            if offset_val < -16 or offset_val > 15:
                raise ParseError("offset must be a value between -16...+15", line)
            return OpRegAddr(REGISTERS[reg_name], offset_val)

    if m := _RE_LABEL_OFFSET.match(inner):
        name = m.group(1)
        sign = m.group(2)
        offset_val = int(m.group(3))
        if sign == "-":
            offset_val = -offset_val
        return OpAddrLabel(name.lower(), offset_val)

    if m := _RE_REG_ONLY.match(inner):
        reg_name = m.group(1).upper()
        if reg_name in REGISTERS:
            return OpRegAddr(REGISTERS[reg_name], 0)

    val = _try_parse_number(inner)
    if val is not None:
        _validate_byte_range(val, line)
        return OpAddr(val)

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
        _validate_byte_range(val, line)
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
_OPERAND_PARSERS: list[Callable[..., Operand | None]] = [
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

    if raw.startswith('"') and raw.endswith('"'):
        return [OpString(raw[1:-1])]

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

        if has_float:
            raise ParseError(
                "DB does not support mixing float and integer operands",
                line,
            )

        if _RE_LABEL.match(part) and _try_parse_number(part) is None:
            raise ParseError("DB does not support this operand", line)

        has_int = True
        val = parse_number(part, line)
        val = _validate_byte_range(val, line)
        operands.append(OpConst(val))
    return operands


# ── Line tokenization ────────────────────────────────────────────────


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
