"""Disassembler core: decode machine code back to assembly text."""

from __future__ import annotations

from pysim8.fp_formats import (
    decode_bfloat16,
    decode_float16,
    decode_float32,
    decode_ofp8_e4m3,
    decode_ofp8_e5m2,
)
from pysim8.isa import (
    BY_CODE,
    BY_CODE_FP,
    FP_CONTROL_MNEMONICS,
    FP_FMT_BF,
    FP_FMT_F,
    FP_FMT_H,
    FP_FMT_O3,
    FP_REGISTERS,
    OpType,
    Reg,
    decode_fpm,
    decode_regaddr,
)

__all__ = ["disasm_insn", "disasm"]

_REG_NAMES: dict[int, str] = {r.value: r.name for r in Reg}


def _build_fpm_to_reg(
    regs: dict[str, tuple[int, int, int, int]],
) -> dict[tuple[int, int, int], str]:
    """Build reverse lookup: (phys, pos, fmt) → shortest register name."""
    result: dict[tuple[int, int, int], str] = {}
    for name, (phys, pos, fmt, _w) in regs.items():
        key = (phys, pos, fmt)
        if key not in result or len(name) < len(result[key]):
            result[key] = name
    return result


_FPM_TO_REG = _build_fpm_to_reg(FP_REGISTERS)

# fmt code → shortest suffix name
_FMT_TO_SUFFIX: dict[int, str] = {0: "F", 1: "H", 2: "BF", 3: "O3", 4: "O2"}


def _decode_fp_imm(raw: int, fmt: int, width: int) -> str:
    """Decode a raw FP immediate to a float literal with suffix."""
    suffix = _FMT_TO_SUFFIX.get(fmt, "?")
    if width == 1:
        v = decode_ofp8_e4m3(raw) if fmt == FP_FMT_O3 else decode_ofp8_e5m2(raw)
    else:
        b2 = bytes([raw & 0xFF, (raw >> 8) & 0xFF])
        if fmt == FP_FMT_H:
            v = decode_float16(b2)
        elif fmt == FP_FMT_BF:
            v = decode_bfloat16(b2)
        elif fmt == FP_FMT_F:
            v = decode_float32(raw.to_bytes(4, "little"))
        else:
            return f"{raw}_{suffix}"
    return f"{v:g}_{suffix}"


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
        case OpType.REG | OpType.REG_ARITH | OpType.REG_GPR | OpType.REG_STACK:
            return _REG_NAMES.get(val, f"?{val}")
        case OpType.IMM:
            return str(val)
        case OpType.MEM:
            return f"[{val}]"
        case OpType.REGADDR:
            return _fmt_regaddr(val)
        case _:
            raise ValueError(f"unknown operand type: {ot}")


def _fmt_fpm(fpm: int) -> tuple[str, int]:
    """Decode FPM byte into (register_name, fmt_code)."""
    phys, pos, fmt = decode_fpm(fpm)
    name = _FPM_TO_REG.get((phys, pos, fmt), f"?FPM({fpm:#x})")
    return name, fmt


def _build_fp_label(mnemonic: str, fp_decoded: list[tuple[str, int]]) -> str:
    if not fp_decoded:
        return mnemonic
    fmts = [_FMT_TO_SUFFIX.get(f, f"?{f}") for _, f in fp_decoded]
    if len(fp_decoded) == 2 and fmts[0] != fmts[1]:
        return f"{mnemonic}.{fmts[0]}.{fmts[1]}"
    return f"{mnemonic}.{fmts[0]}"


def _disasm_fp_insn(opcode: int, raw_operands: tuple[int, ...]) -> str | None:
    """Disassemble one FP instruction. Returns None if opcode not FP."""
    defn = BY_CODE_FP.get(opcode)
    if defn is None:
        return None

    mnemonic = defn.mnemonic
    if mnemonic in FP_CONTROL_MNEMONICS:
        parts = [_fmt_operand(ot, val) for ot, val in zip(defn.sig, raw_operands)]
        return f"{mnemonic} {', '.join(parts)}" if parts else mnemonic

    fp_count = sum(1 for ot in defn.sig if ot == OpType.FP_REG)
    fp_decoded: list[tuple[str, int]] = [_fmt_fpm(b) for b in raw_operands[:fp_count]]
    fp_iter = iter(fp_decoded)
    non_fp_iter = iter(raw_operands[fp_count:])
    fmt_code = -1
    parts = []

    for ot in defn.sig:
        if ot == OpType.FP_REG:
            name, fmt_code = next(fp_iter)
            parts.append(name)
        elif ot == OpType.FP_IMM8:
            parts.append(_decode_fp_imm(next(non_fp_iter), fmt_code, 1))
        elif ot == OpType.FP_IMM16:
            lo, hi = next(non_fp_iter), next(non_fp_iter)
            parts.append(_decode_fp_imm(lo | (hi << 8), fmt_code, 2))
        else:
            parts.append(_fmt_operand(ot, next(non_fp_iter)))

    label = _build_fp_label(mnemonic, fp_decoded)
    return f"{label} {', '.join(parts)}" if parts else label


def disasm_insn(opcode: int, operands: tuple[int, ...] = ()) -> str:
    """Disassemble one instruction to text, e.g. 'MOV A, 42'."""
    defn = BY_CODE.get(opcode)
    if defn is not None:
        ops = [_fmt_operand(ot, val) for ot, val in zip(defn.sig, operands)]
        if ops:
            return f"{defn.mnemonic} {', '.join(ops)}"
        return defn.mnemonic

    # Try FP instruction
    result = _disasm_fp_insn(opcode, operands)
    if result is not None:
        return result

    return f"??? ({opcode})"


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
            defn = BY_CODE_FP.get(opcode)
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
