"""ISA definitions: opcodes, registers, constants, and instruction table."""

from dataclasses import dataclass
from enum import Enum, IntEnum

from pysim8._isa_tables import (
    FP_REG_DATA as _FP_REG_DATA,
)
from pysim8._isa_tables import (
    ISA_DATA as _ISA_DATA,
)
from pysim8._isa_tables import (
    ISA_FP_DATA as _ISA_FP_DATA,
)
from pysim8._isa_tables import (
    ISA_VU_DATA as _ISA_VU_DATA,
)
from pysim8._isa_tables import (
    MNEMONIC_ALIASES,
    Op,
)
from pysim8.constants import (
    FP_FMT_BF,
    FP_FMT_F,
    FP_FMT_H,
    FP_FMT_MAX_POS,
    FP_FMT_N1,
    FP_FMT_N2,
    FP_FMT_O2,
    FP_FMT_O3,
    FP_FMT_WIDTH,
    IO_START,
    MEMORY_SIZE,
    PAGE_SIZE,
    SP_INIT,
)

__all__ = [
    "Op",
    "Reg",
    "REGISTERS",
    "ARITH_CODES",
    "GPR_CODES",
    "STACK_CODES",
    "MNEMONIC_ALIASES",
    "OpType",
    "InstrDef",
    "ISA",
    "BY_CODE",
    "BY_MNEMONIC",
    "MNEMONICS",
    "encode_regaddr",
    "decode_regaddr",
    "ISA_FP",
    "BY_CODE_FP",
    "BY_MNEMONIC_FP",
    "MNEMONICS_FP",
    "FP_CONTROL_MNEMONICS",
    "FpRegInfo",
    "FP_REGISTERS",
    "FP_SUFFIX_TO_FMT",
    "FP_FMT_F",
    "FP_FMT_H",
    "FP_FMT_BF",
    "FP_FMT_O3",
    "FP_FMT_O2",
    "FP_FMT_N1",
    "FP_FMT_N2",
    "FP_FMT_WIDTH",
    "FP_FMT_MAX_POS",
    "FP_WIDTH_REGS",
    "FORBIDDEN_FP_LABEL_NAMES",
    "encode_fpm",
    "decode_fpm",
    "validate_fpm",
    "MEMORY_SIZE",
    "PAGE_SIZE",
    "IO_START",
    "SP_INIT",
    "ISA_VU",
    "BY_CODE_VU",
    "BY_MNEMONIC_VU",
    "MNEMONICS_VU",
    "VU_REGISTERS",
    "VU_SUFFIX_TO_FMT",
    "VU_SUFFIX_TO_MODE",
    "VU_CMP_SUFFIX",
    "VU_FMT_ELEM_SIZE",
    "VU_WINDOW_BYTES",
    "VU_WINDOW_SIZE",
    "VU_ASYNC_OPS",
    "VU_ARITH_OPS",
    "VU_UNARY_OPS",
    "VU_VV_ONLY_OPS",
    "VU_INT_FMTS",
    "VU_SYNC_MNEMONICS",
    "VU_MODE_VV",
    "VU_MODE_VS",
    "VU_MODE_VI",
    "VU_MODE_R",
    "encode_vfm",
    "decode_vfm",
    "encode_vu_regs",
    "decode_vu_regs",
    "vu_instr_size",
]


class Reg(IntEnum):
    """Register codes."""

    A = 0
    B = 1
    C = 2
    D = 3
    SP = 4
    DP = 5


# Map of register name (uppercase) → Reg code
REGISTERS: dict[str, Reg] = {r.name: r for r in Reg}

# Register hierarchy (more special → fewer allowed operations):
#   REG       = A B C D SP DP  — MOV only
#   REG_ARITH = A B C D SP     — MOV + arithmetic (ADD, SUB, CMP, INC, DEC)
#   REG_GPR   = A B C D        — MOV + arithmetic + logic/shift/stack/jump
#   REG_STACK  = A B C D DP     — PUSH/POP (GPR + DP)
GPR_CODES: frozenset[int] = frozenset({Reg.A, Reg.B, Reg.C, Reg.D})
ARITH_CODES: frozenset[int] = GPR_CODES | {Reg.SP}
STACK_CODES: frozenset[int] = GPR_CODES | {Reg.DP}

# ── REGADDR encoding ──────────────────────────────────────────────────
#
# Register-indirect operands ([B], [C+3], [D-1]) are packed into one byte:
#
#   bit  7 6 5 4 3  2 1 0
#        ┌─offset──┐ ┌reg┐
#
#   reg    — 3-bit register code (0..5, same as Reg enum)
#   offset — 5-bit signed offset in two's complement (−16 .. +15)
#
# Examples:
#   [A]    → reg=0, offset=0  → 0b00000_000 = 0x00
#   [B+3]  → reg=1, offset=3  → 0b00011_001 = 0x19
#   [C-1]  → reg=2, offset=-1 → 0b11111_010 = 0xFA

_RA_REG_BITS = 3
_RA_REG_MASK = (1 << _RA_REG_BITS) - 1  # 0x07
_RA_OFF_RANGE = 1 << (8 - _RA_REG_BITS)  # 32
_RA_OFF_MAX = _RA_OFF_RANGE // 2 - 1  # 15


def encode_regaddr(reg_code: int, offset: int) -> int:
    """Encode [reg±offset] into a single byte."""
    if reg_code < 0 or reg_code > 5:
        raise ValueError(f"Invalid register code: {reg_code}")
    if offset < -16 or offset > 15:
        raise ValueError(f"Offset out of range -16..+15: {offset}")
    offset_u = offset if offset >= 0 else _RA_OFF_RANGE + offset
    return (offset_u << _RA_REG_BITS) | reg_code


def decode_regaddr(encoded: int) -> tuple[int, int]:
    """Decode a REGADDR byte into (reg_code, offset)."""
    reg_code = encoded & _RA_REG_MASK
    offset_u = encoded >> _RA_REG_BITS
    offset = offset_u if offset_u <= _RA_OFF_MAX else offset_u - _RA_OFF_RANGE
    return reg_code, offset


# Short suffix -> fmt code (case-insensitive matching done by caller)
FP_SUFFIX_TO_FMT: dict[str, int] = {
    "F": FP_FMT_F,
    "E8M23": FP_FMT_F,
    "H": FP_FMT_H,
    "E5M10": FP_FMT_H,
    "BF": FP_FMT_BF,
    "E8M7": FP_FMT_BF,
    "O3": FP_FMT_O3,
    "E4M3": FP_FMT_O3,
    "O2": FP_FMT_O2,
    "E5M2": FP_FMT_O2,
    "N1": FP_FMT_N1,
    "E2M1": FP_FMT_N1,
    "N2": FP_FMT_N2,
    "E1M2": FP_FMT_N2,
}


@dataclass(frozen=True, slots=True)
class FpRegInfo:
    phys: int
    pos: int
    fmt: int
    width: int


FP_REGISTERS: dict[str, FpRegInfo] = {name: FpRegInfo(*info) for name, info in _FP_REG_DATA.items()}

# Width class -> allowed FP register names
FP_WIDTH_REGS: dict[int, frozenset[str]] = {
    32: frozenset({"FA", "FB"}),
    16: frozenset({"FHA", "FHB", "FHC", "FHD"}),
    8: frozenset({"FQA", "FQB", "FQC", "FQD", "FQE", "FQF", "FQG", "FQH"}),
    4: frozenset(
        {"FOA", "FOB", "FOC", "FOD", "FOE", "FOF", "FOG", "FOH", "FOI", "FOJ", "FOK", "FOL", "FOM", "FON", "FOO", "FOP"}
    ),
}


# FP names forbidden as labels: real v2 registers + future-reserved names (spec §5.3).
# FC/FD = phys 2/3 full; FHE-FHH = phys 2/3 half; FQI-FQP = phys 2/3 quarter.
FORBIDDEN_FP_LABEL_NAMES: frozenset[str] = frozenset(
    FP_REGISTERS.keys()
    | {"FC", "FD", "FHE", "FHF", "FHG", "FHH", "FQI", "FQJ", "FQK", "FQL", "FQM", "FQN", "FQO", "FQP"}
)


def encode_fpm(phys: int, pos: int, fmt: int) -> int:
    """Encode FPM byte: (phys << 6) | (pos << 3) | fmt."""
    return (phys << 6) | (pos << 3) | fmt


def decode_fpm(fpm: int) -> tuple[int, int, int]:
    """Decode FPM byte -> (phys, pos, fmt)."""
    return (fpm >> 6) & 0x03, (fpm >> 3) & 0x07, fpm & 0x07


def validate_fpm(fpm: int) -> bool:
    """Check if FPM byte is valid for v2."""
    phys, pos, fmt = decode_fpm(fpm)
    if phys > 1:
        return False
    if fmt >= 5:
        return False
    return pos <= FP_FMT_MAX_POS[fmt]


# ── Instruction definitions ────────────────────────────────────────


class OpType(Enum):
    """Operand type for instruction matching."""

    REG = "reg"  # any register (0-5)
    REG_ARITH = "reg_arith"  # GPR + SP (0-4)
    REG_GPR = "reg_gpr"  # GPR only (0-3)
    REG_STACK = "reg_stack"  # GPR + DP (0-3, 5) — PUSH/POP
    IMM = "imm"  # number or label (no brackets)
    MEM = "mem"  # [addr] — direct address in brackets
    REGADDR = "regaddr"  # [reg±offset] — register indirect
    FP_REG = "fp_reg"  # FP register operand
    FP_IMM8 = "fp_imm8"  # 8-bit FP immediate (1 byte)
    FP_IMM16 = "fp_imm16"  # 16-bit FP immediate (2 bytes, LE)


_OPTYPE_BYTES: dict[str, int] = {
    OpType.FP_IMM16.value: 2,
}


@dataclass(frozen=True, slots=True)
class InstrDef:
    """Definition of one instruction variant.

    For format-dependent FP ops (format_dep=True), ``cost`` is the FPU overhead
    added on top of the memory access cost (mem_cost[fmt]).  For all other ops
    ``cost`` is the full static cycle count.
    """

    op: Op
    mnemonic: str
    sig: tuple[OpType, ...]
    cost: int = 1  # clock cycles (or FPU overhead when format_dep=True)
    format_dep: bool = False  # True → cost = mem_cost[fmt] + cost

    @property
    def size(self) -> int:
        return 1 + sum(_OPTYPE_BYTES.get(ot.value, 1) for ot in self.sig)


_OPTYPE_MAP: dict[str, OpType] = {ot.value: ot for ot in OpType}


def _build_isa(data: list[tuple[str, int, str, list[str], int, bool]]) -> tuple[InstrDef, ...]:
    return tuple(InstrDef(Op(row[1]), row[2], tuple(_OPTYPE_MAP[t] for t in row[3]), row[4], row[5]) for row in data)


def _by_mnemonic(instrs: tuple[InstrDef, ...]) -> dict[str, tuple[InstrDef, ...]]:
    result: dict[str, list[InstrDef]] = {}
    for instr in instrs:
        result.setdefault(instr.mnemonic, []).append(instr)
    return {k: tuple(v) for k, v in result.items()}


ISA: tuple[InstrDef, ...] = _build_isa(_ISA_DATA)
BY_CODE: dict[int, InstrDef] = {int(instr.op): instr for instr in ISA}
BY_MNEMONIC: dict[str, tuple[InstrDef, ...]] = _by_mnemonic(ISA)
MNEMONICS: frozenset[str] = frozenset(BY_MNEMONIC) | {"DB"}

# ── FP ISA ────────────────────────────────────────────────────────

ISA_FP: tuple[InstrDef, ...] = _build_isa(_ISA_FP_DATA)
BY_CODE_FP: dict[int, InstrDef] = {int(instr.op): instr for instr in ISA_FP}
BY_MNEMONIC_FP: dict[str, tuple[InstrDef, ...]] = _by_mnemonic(ISA_FP)
MNEMONICS_FP: frozenset[str] = frozenset(BY_MNEMONIC_FP)
FP_CONTROL_MNEMONICS: frozenset[str] = frozenset({"FSTAT", "FCFG", "FSCFG", "FCLR"})

# ── VU constants ─────────────────────────────────────────────────

# VU format codes (fmt field in VFM byte)
VU_FMT_F = 0  # float32
VU_FMT_H = 1  # float16
VU_FMT_BF = 2  # bfloat16
VU_FMT_O3 = 3  # OFP8 E4M3
VU_FMT_O2 = 4  # OFP8 E5M2
VU_FMT_U = 5  # UINT8
VU_FMT_I = 6  # INT8

# VU format → element size in bytes
VU_FMT_ELEM_SIZE: dict[int, int] = {
    VU_FMT_F: 4,
    VU_FMT_H: 2,
    VU_FMT_BF: 2,
    VU_FMT_O3: 1,
    VU_FMT_O2: 1,
    VU_FMT_U: 1,
    VU_FMT_I: 1,
}

# VU memory port: 8 bytes/tick → window = 8 / elem_size elements
VU_WINDOW_BYTES: int = 8
VU_WINDOW_SIZE: dict[int, int] = {1: 8, 2: 4, 4: 2}

# VU mode codes
VU_MODE_VV = 0
VU_MODE_VS = 1
VU_MODE_VI = 2
VU_MODE_R = 3  # reduction

# VU format suffix → fmt code
VU_SUFFIX_TO_FMT: dict[str, int] = {
    "F": VU_FMT_F,
    "H": VU_FMT_H,
    "BF": VU_FMT_BF,
    "O3": VU_FMT_O3,
    "O2": VU_FMT_O2,
    "U": VU_FMT_U,
    "I": VU_FMT_I,
}

# VU mode suffix → mode code
VU_SUFFIX_TO_MODE: dict[str, int] = {
    "VV": VU_MODE_VV,
    "VS": VU_MODE_VS,
    "VI": VU_MODE_VI,
    "R": VU_MODE_R,
}

# VU register names → code
VU_REGISTERS: dict[str, int] = {
    "VA": 0,
    "VB": 1,
    "VC": 2,
    "VM": 3,
    "VL": 4,
}

# VU comparison condition codes (VCMP only)
VU_CMP_EQ = 0
VU_CMP_NE = 1
VU_CMP_LT = 2
VU_CMP_LE = 3
VU_CMP_GT = 4
VU_CMP_GE = 5

VU_CMP_SUFFIX: dict[str, int] = {
    "EQ": VU_CMP_EQ,
    "NE": VU_CMP_NE,
    "LT": VU_CMP_LT,
    "LE": VU_CMP_LE,
    "GT": VU_CMP_GT,
    "GE": VU_CMP_GE,
}

# Async opcodes that support each mode set
VU_ARITH_OPS: frozenset[int] = frozenset(
    {
        Op.VADD,
        Op.VSUB,
        Op.VMUL,
        Op.VDIV,
        Op.VMAX,
        Op.VMIN,
    }
)
VU_UNARY_OPS: frozenset[int] = frozenset({Op.VSQRT, Op.VNEG, Op.VABS})
VU_ASYNC_OPS: frozenset[int] = frozenset(
    {
        Op.VADD,
        Op.VSUB,
        Op.VMUL,
        Op.VDIV,
        Op.VMAX,
        Op.VMIN,
        Op.VDOT,
        Op.VSQRT,
        Op.VNEG,
        Op.VABS,
        Op.VCMP,
        Op.VSEL,
        Op.VMOV,
    }
)
VU_VV_ONLY_OPS: frozenset[int] = frozenset({Op.VDOT, Op.VCMP, Op.VSEL})
VU_INT_FMTS: frozenset[int] = frozenset({VU_FMT_U, VU_FMT_I})


def encode_vfm(fmt: int, mode: int) -> int:
    """Encode VFM byte: (mode << 3) | fmt."""
    return (mode << 3) | fmt


def decode_vfm(vfm: int) -> tuple[int, int, int]:
    """Decode VFM byte → (fmt, mode, cond). cond is always 0 in VFM (encoded as 4th byte for VCMP)."""
    return vfm & 0x07, (vfm >> 3) & 0x03, 0


def encode_vu_regs(dst: int, src1: int, src2: int) -> int:
    """Encode register operand byte: (dst << 6) | (src1 << 4) | (src2 << 2)."""
    return (dst << 6) | (src1 << 4) | (src2 << 2)


def decode_vu_regs(regs: int) -> tuple[int, int, int]:
    """Decode register operand byte → (dst, src1, src2)."""
    return (regs >> 6) & 0x03, (regs >> 4) & 0x03, (regs >> 2) & 0x03


def vu_instr_size(opcode: int, vfm: int) -> int:
    """Compute instruction size for a VU opcode given VFM byte.

    Sync opcodes: fixed size from ISA_VU.
    Async opcodes: 3 for .vv/.vs/.r, 3 + elem_size for .vi.
    VCMP is always 4 bytes (opcode + VFM + regs + cond).
    """
    if opcode == Op.VCMP:
        return 4
    if opcode not in VU_ASYNC_OPS:
        defn = BY_CODE_VU.get(opcode)
        return defn.size if defn is not None else 1
    fmt, mode, _ = decode_vfm(vfm)
    if mode == VU_MODE_VI:
        return 3 + VU_FMT_ELEM_SIZE.get(fmt, 1)
    return 3


# ── VU ISA ────────────────────────────────────────────────────────

ISA_VU: tuple[InstrDef, ...] = _build_isa(_ISA_VU_DATA)
BY_CODE_VU: dict[int, InstrDef] = {int(instr.op): instr for instr in ISA_VU}
BY_MNEMONIC_VU: dict[str, tuple[InstrDef, ...]] = _by_mnemonic(ISA_VU)
MNEMONICS_VU: frozenset[str] = frozenset(BY_MNEMONIC_VU)
VU_SYNC_MNEMONICS: frozenset[str] = frozenset({"VSET", "VFSTAT", "VFCLR", "VWAIT"})
