"""ISA definitions: opcodes, registers, constants, and instruction table."""

from dataclasses import dataclass
from enum import Enum, IntEnum

__all__ = [
    "Op", "Reg", "REGISTERS", "GPR_CODES", "STACK_CODES", "MNEMONIC_ALIASES",
    "Ot", "InsnDef", "ISA", "BY_CODE", "BY_MNEMONIC", "MNEMONICS",
    "encode_regaddr", "decode_regaddr",
]


class Op(IntEnum):
    """CPU opcodes (decimal values from spec/opcodes.md)."""

    HLT = 0

    # MOV — Data Movement (1-8)
    MOV_REG_REG = 1
    MOV_REG_ADDR = 2
    MOV_REG_REGADDR = 3
    MOV_ADDR_REG = 4
    MOV_REGADDR_REG = 5
    MOV_REG_CONST = 6
    MOV_ADDR_CONST = 7
    MOV_REGADDR_CONST = 8

    # ADD (10-13)
    ADD_REG_REG = 10
    ADD_REG_REGADDR = 11
    ADD_REG_ADDR = 12
    ADD_REG_CONST = 13

    # SUB (14-17)
    SUB_REG_REG = 14
    SUB_REG_REGADDR = 15
    SUB_REG_ADDR = 16
    SUB_REG_CONST = 17

    # INC / DEC (18-19)
    INC_REG = 18
    DEC_REG = 19

    # CMP (20-23)
    CMP_REG_REG = 20
    CMP_REG_REGADDR = 21
    CMP_REG_ADDR = 22
    CMP_REG_CONST = 23

    # JMP (30-31)
    JMP_REG = 30
    JMP_ADDR = 31

    # JC (32-33)
    JC_REG = 32
    JC_ADDR = 33

    # JNC (34-35)
    JNC_REG = 34
    JNC_ADDR = 35

    # JZ (36-37)
    JZ_REG = 36
    JZ_ADDR = 37

    # JNZ (38-39)
    JNZ_REG = 38
    JNZ_ADDR = 39

    # JA (40-41)
    JA_REG = 40
    JA_ADDR = 41

    # JNA (42-43)
    JNA_REG = 42
    JNA_ADDR = 43

    # PUSH (50-53)
    PUSH_REG = 50
    PUSH_REGADDR = 51
    PUSH_ADDR = 52
    PUSH_CONST = 53

    # POP (54)
    POP_REG = 54

    # CALL (55-56)
    CALL_REG = 55
    CALL_ADDR = 56

    # RET (57)
    RET = 57

    # MUL (60-63)
    MUL_REG = 60
    MUL_REGADDR = 61
    MUL_ADDR = 62
    MUL_CONST = 63

    # DIV (64-67)
    DIV_REG = 64
    DIV_REGADDR = 65
    DIV_ADDR = 66
    DIV_CONST = 67

    # AND (70-73)
    AND_REG_REG = 70
    AND_REG_REGADDR = 71
    AND_REG_ADDR = 72
    AND_REG_CONST = 73

    # OR (74-77)
    OR_REG_REG = 74
    OR_REG_REGADDR = 75
    OR_REG_ADDR = 76
    OR_REG_CONST = 77

    # XOR (78-81)
    XOR_REG_REG = 78
    XOR_REG_REGADDR = 79
    XOR_REG_ADDR = 80
    XOR_REG_CONST = 81

    # NOT (82)
    NOT_REG = 82

    # SHL (90-93)
    SHL_REG_REG = 90
    SHL_REG_REGADDR = 91
    SHL_REG_ADDR = 92
    SHL_REG_CONST = 93

    # SHR (94-97)
    SHR_REG_REG = 94
    SHR_REG_REGADDR = 95
    SHR_REG_ADDR = 96
    SHR_REG_CONST = 97


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
#   REG_STACK = A B C D SP     — MOV + arithmetic (ADD, SUB, CMP, INC, DEC)
#   REG_GPR   = A B C D        — MOV + arithmetic + logic/shift/stack/jump
GPR_CODES: frozenset[int] = frozenset({Reg.A, Reg.B, Reg.C, Reg.D})
STACK_CODES: frozenset[int] = GPR_CODES | {Reg.SP}

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
_RA_OFF_MAX = _RA_OFF_RANGE // 2 - 1     # 15


def encode_regaddr(reg_code: int, offset: int) -> int:
    """Encode [reg±offset] into a single byte."""
    offset_u = offset if offset >= 0 else _RA_OFF_RANGE + offset
    return (offset_u << _RA_REG_BITS) | reg_code


def decode_regaddr(encoded: int) -> tuple[int, int]:
    """Decode a REGADDR byte into (reg_code, offset)."""
    reg_code = encoded & _RA_REG_MASK
    offset_u = encoded >> _RA_REG_BITS
    offset = offset_u if offset_u <= _RA_OFF_MAX else offset_u - _RA_OFF_RANGE
    return reg_code, offset


# Mnemonic aliases → canonical mnemonic
MNEMONIC_ALIASES: dict[str, str] = {
    "JB": "JC",
    "JNAE": "JC",
    "JNB": "JNC",
    "JAE": "JNC",
    "JE": "JZ",
    "JNE": "JNZ",
    "JNBE": "JA",
    "JBE": "JNA",
    # SAL/SAR → SHL/SHR
    "SAL": "SHL",
    "SAR": "SHR",
}


# ── Instruction definitions ────────────────────────────────────────


class Ot(Enum):
    """Operand type for instruction matching."""

    REG = "reg"              # any register (0-5)
    REG_STACK = "reg_stack"  # GPR + SP (0-4)
    REG_GPR = "reg_gpr"      # GPR only (0-3)
    IMM = "imm"          # number or label (no brackets)
    MEM = "mem"          # [addr] — direct address in brackets
    REGADDR = "regaddr"  # [reg±offset] — register indirect


@dataclass(frozen=True, slots=True)
class InsnDef:
    """Definition of one instruction variant."""

    op: Op
    mnemonic: str
    sig: tuple[Ot, ...]
    cost: int = 1  # cost in clock cycles

    @property
    def size(self) -> int:
        return 1 + len(self.sig)


_REG, _STK, _GPR = Ot.REG, Ot.REG_STACK, Ot.REG_GPR
_IMM, _MEM, _IADDR = Ot.IMM, Ot.MEM, Ot.REGADDR

ISA: tuple[InsnDef, ...] = (
    # HLT (0)
    InsnDef(Op.HLT, "HLT", (), cost=0),
    # MOV (1-8)
    InsnDef(Op.MOV_REG_REG, "MOV", (_REG, _REG)),
    InsnDef(Op.MOV_REG_ADDR, "MOV", (_REG, _MEM), cost=2),
    InsnDef(Op.MOV_REG_REGADDR, "MOV", (_REG, _IADDR), cost=2),
    InsnDef(Op.MOV_ADDR_REG, "MOV", (_MEM, _REG), cost=2),
    InsnDef(Op.MOV_REGADDR_REG, "MOV", (_IADDR, _REG), cost=2),
    InsnDef(Op.MOV_REG_CONST, "MOV", (_REG, _IMM)),
    InsnDef(Op.MOV_ADDR_CONST, "MOV", (_MEM, _IMM), cost=2),
    InsnDef(Op.MOV_REGADDR_CONST, "MOV", (_IADDR, _IMM), cost=2),
    # ADD (10-13)
    InsnDef(Op.ADD_REG_REG, "ADD", (_STK, _STK)),
    InsnDef(Op.ADD_REG_REGADDR, "ADD", (_STK, _IADDR), cost=3),
    InsnDef(Op.ADD_REG_ADDR, "ADD", (_STK, _MEM), cost=3),
    InsnDef(Op.ADD_REG_CONST, "ADD", (_STK, _IMM)),
    # SUB (14-17)
    InsnDef(Op.SUB_REG_REG, "SUB", (_STK, _STK)),
    InsnDef(Op.SUB_REG_REGADDR, "SUB", (_STK, _IADDR), cost=3),
    InsnDef(Op.SUB_REG_ADDR, "SUB", (_STK, _MEM), cost=3),
    InsnDef(Op.SUB_REG_CONST, "SUB", (_STK, _IMM)),
    # INC / DEC (18-19)
    InsnDef(Op.INC_REG, "INC", (_STK,)),
    InsnDef(Op.DEC_REG, "DEC", (_STK,)),
    # CMP (20-23)
    InsnDef(Op.CMP_REG_REG, "CMP", (_STK, _STK)),
    InsnDef(Op.CMP_REG_REGADDR, "CMP", (_STK, _IADDR), cost=3),
    InsnDef(Op.CMP_REG_ADDR, "CMP", (_STK, _MEM), cost=3),
    InsnDef(Op.CMP_REG_CONST, "CMP", (_STK, _IMM)),
    # JMP (30-31)
    InsnDef(Op.JMP_REG, "JMP", (_GPR,)),
    InsnDef(Op.JMP_ADDR, "JMP", (_IMM,)),
    # JC (32-33)
    InsnDef(Op.JC_REG, "JC", (_GPR,)),
    InsnDef(Op.JC_ADDR, "JC", (_IMM,)),
    # JNC (34-35)
    InsnDef(Op.JNC_REG, "JNC", (_GPR,)),
    InsnDef(Op.JNC_ADDR, "JNC", (_IMM,)),
    # JZ (36-37)
    InsnDef(Op.JZ_REG, "JZ", (_GPR,)),
    InsnDef(Op.JZ_ADDR, "JZ", (_IMM,)),
    # JNZ (38-39)
    InsnDef(Op.JNZ_REG, "JNZ", (_GPR,)),
    InsnDef(Op.JNZ_ADDR, "JNZ", (_IMM,)),
    # JA (40-41)
    InsnDef(Op.JA_REG, "JA", (_GPR,)),
    InsnDef(Op.JA_ADDR, "JA", (_IMM,)),
    # JNA (42-43)
    InsnDef(Op.JNA_REG, "JNA", (_GPR,)),
    InsnDef(Op.JNA_ADDR, "JNA", (_IMM,)),
    # PUSH (50-53)
    InsnDef(Op.PUSH_REG, "PUSH", (_GPR,), cost=2),
    InsnDef(Op.PUSH_REGADDR, "PUSH", (_IADDR,), cost=4),
    InsnDef(Op.PUSH_ADDR, "PUSH", (_MEM,), cost=4),
    InsnDef(Op.PUSH_CONST, "PUSH", (_IMM,), cost=2),
    # POP (54)
    InsnDef(Op.POP_REG, "POP", (_GPR,), cost=2),
    # CALL (55-56)
    InsnDef(Op.CALL_REG, "CALL", (_GPR,), cost=2),
    InsnDef(Op.CALL_ADDR, "CALL", (_IMM,), cost=2),
    # RET (57)
    InsnDef(Op.RET, "RET", (), cost=2),
    # MUL (60-63)
    InsnDef(Op.MUL_REG, "MUL", (_GPR,), cost=2),
    InsnDef(Op.MUL_REGADDR, "MUL", (_IADDR,), cost=4),
    InsnDef(Op.MUL_ADDR, "MUL", (_MEM,), cost=4),
    InsnDef(Op.MUL_CONST, "MUL", (_IMM,), cost=2),
    # DIV (64-67)
    InsnDef(Op.DIV_REG, "DIV", (_GPR,), cost=2),
    InsnDef(Op.DIV_REGADDR, "DIV", (_IADDR,), cost=4),
    InsnDef(Op.DIV_ADDR, "DIV", (_MEM,), cost=4),
    InsnDef(Op.DIV_CONST, "DIV", (_IMM,), cost=2),
    # AND (70-73)
    InsnDef(Op.AND_REG_REG, "AND", (_GPR, _GPR)),
    InsnDef(Op.AND_REG_REGADDR, "AND", (_GPR, _IADDR), cost=3),
    InsnDef(Op.AND_REG_ADDR, "AND", (_GPR, _MEM), cost=3),
    InsnDef(Op.AND_REG_CONST, "AND", (_GPR, _IMM)),
    # OR (74-77)
    InsnDef(Op.OR_REG_REG, "OR", (_GPR, _GPR)),
    InsnDef(Op.OR_REG_REGADDR, "OR", (_GPR, _IADDR), cost=3),
    InsnDef(Op.OR_REG_ADDR, "OR", (_GPR, _MEM), cost=3),
    InsnDef(Op.OR_REG_CONST, "OR", (_GPR, _IMM)),
    # XOR (78-81)
    InsnDef(Op.XOR_REG_REG, "XOR", (_GPR, _GPR)),
    InsnDef(Op.XOR_REG_REGADDR, "XOR", (_GPR, _IADDR), cost=3),
    InsnDef(Op.XOR_REG_ADDR, "XOR", (_GPR, _MEM), cost=3),
    InsnDef(Op.XOR_REG_CONST, "XOR", (_GPR, _IMM)),
    # NOT (82)
    InsnDef(Op.NOT_REG, "NOT", (_GPR,)),
    # SHL (90-93)
    InsnDef(Op.SHL_REG_REG, "SHL", (_GPR, _GPR)),
    InsnDef(Op.SHL_REG_REGADDR, "SHL", (_GPR, _IADDR), cost=3),
    InsnDef(Op.SHL_REG_ADDR, "SHL", (_GPR, _MEM), cost=3),
    InsnDef(Op.SHL_REG_CONST, "SHL", (_GPR, _IMM)),
    # SHR (94-97)
    InsnDef(Op.SHR_REG_REG, "SHR", (_GPR, _GPR)),
    InsnDef(Op.SHR_REG_REGADDR, "SHR", (_GPR, _IADDR), cost=3),
    InsnDef(Op.SHR_REG_ADDR, "SHR", (_GPR, _MEM), cost=3),
    InsnDef(Op.SHR_REG_CONST, "SHR", (_GPR, _IMM)),
)

# ── Derived lookups ────────────────────────────────────────────────

BY_CODE: dict[int, InsnDef] = {int(insn.op): insn for insn in ISA}

_by_mn: dict[str, list[InsnDef]] = {}
for _insn in ISA:
    _by_mn.setdefault(_insn.mnemonic, []).append(_insn)
BY_MNEMONIC: dict[str, tuple[InsnDef, ...]] = {
    k: tuple(v) for k, v in _by_mn.items()
}
del _by_mn, _insn, _REG, _STK, _GPR, _IMM, _MEM, _IADDR

MNEMONICS: frozenset[str] = frozenset(BY_MNEMONIC) | {"DB"}
