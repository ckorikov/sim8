"""Operand types, exceptions, and parsed line for the assembly parser."""

from __future__ import annotations

from dataclasses import dataclass

__all__ = [
    "AsmError",
    "ParseError",
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
    "Operand",
    "ParsedLine",
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
