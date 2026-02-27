"""Disassembler core: decode machine code back to assembly text."""

from __future__ import annotations

from pysim8.isa import BY_CODE, OpType, Reg, decode_regaddr

__all__ = ["disasm_insn", "disasm"]

_REG_NAMES: dict[int, str] = {r.value: r.name for r in Reg}


def _fmt_regaddr(val: int) -> str:
    """Format encoded REGADDR byte as [reg±offset]."""
    reg_code, offset = decode_regaddr(val)
    name = _REG_NAMES.get(reg_code, f"?{reg_code}")
    if offset > 0:
        return f"[{name}+{offset}]"
    if offset < 0:
        return f"[{name}{offset}]"
    return f"[{name}]"


def _fmt_operand(ot: OpType, val: int) -> str:
    match ot:
        case OpType.REG | OpType.REG_STACK | OpType.REG_GPR:
            return _REG_NAMES.get(val, f"?{val}")
        case OpType.IMM:
            return str(val)
        case OpType.MEM:
            return f"[{val}]"
        case OpType.REGADDR:
            return _fmt_regaddr(val)
        case _:
            raise ValueError(f"unknown operand type: {ot}")


def disasm_insn(opcode: int, operands: tuple[int, ...] = ()) -> str:
    """Disassemble one instruction to text, e.g. 'MOV A, 42'."""
    defn = BY_CODE.get(opcode)
    if defn is None:
        return f"??? ({opcode})"
    ops = [_fmt_operand(ot, val) for ot, val in zip(defn.sig, operands)]
    if ops:
        return f"{defn.mnemonic} {', '.join(ops)}"
    return defn.mnemonic


def disasm(code: bytes | list[int]) -> list[tuple[int, str, int]]:
    """Disassemble a byte stream.

    Returns list of (address, text, size) tuples.
    Unknown opcodes emit 'DB <value>'.
    """
    result: list[tuple[int, str, int]] = []
    i = 0
    while i < len(code):
        opcode = code[i]
        defn = BY_CODE.get(opcode)
        if defn is None:
            result.append((i, f"DB {opcode}", 1))
            i += 1
            continue
        size = defn.size
        if i + size > len(code):
            result.append((i, f"DB {opcode}", 1))
            i += 1
            continue
        operands = tuple(code[i + k] for k in range(1, size))
        result.append((i, disasm_insn(opcode, operands), size))
        i += size
    return result
