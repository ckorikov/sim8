"""Disassembler core: decode machine code back to assembly text."""

from __future__ import annotations

from pysim8.isa import (
    BY_CODE, BY_CODE_FP, OpType, Reg,
    FP_REGISTERS, FP_CONTROL_MNEMONICS,
    decode_fpm, decode_regaddr,
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


def _fmt_fpm(fpm: int) -> tuple[str, int]:
    """Decode FPM byte into (register_name, fmt_code)."""
    phys, pos, fmt = decode_fpm(fpm)
    name = _FPM_TO_REG.get((phys, pos, fmt), f"?FPM({fpm:#x})")
    return name, fmt


def _disasm_fp_insn(opcode: int, raw_operands: tuple[int, ...]) -> str | None:
    """Disassemble one FP instruction. Returns None if opcode not FP."""
    defn = BY_CODE_FP.get(opcode)
    if defn is None:
        return None

    sig = defn.sig
    mnemonic = defn.mnemonic

    # Control instructions (FSTAT, FCFG, FSCFG, FCLR): no FPM reordering
    if mnemonic in FP_CONTROL_MNEMONICS:
        parts = [_fmt_operand(ot, val) for ot, val in zip(sig, raw_operands)]
        if parts:
            return f"{mnemonic} {', '.join(parts)}"
        return mnemonic

    # Count FP_REG operands to split raw bytes: [FPM...][non-FP...]
    fp_indices = [i for i, ot in enumerate(sig) if ot == OpType.FP_REG]
    non_fp_indices = [
        i for i, ot in enumerate(sig) if ot != OpType.FP_REG
    ]

    fp_count = len(fp_indices)

    # Split raw operand bytes
    fpm_bytes = raw_operands[:fp_count]
    non_fp_bytes = raw_operands[fp_count:]

    # Decode FPM bytes
    fp_decoded: list[tuple[str, int]] = [_fmt_fpm(b) for b in fpm_bytes]

    # Build output operands in sig order
    parts: list[str] = []
    fp_iter = iter(fp_decoded)
    non_fp_iter = iter(non_fp_bytes)
    fmt_code = -1

    for ot in sig:
        if ot == OpType.FP_REG:
            name, fmt_code = next(fp_iter)
            parts.append(name)
        elif ot == OpType.FP_IMM8:
            imm = next(non_fp_iter)
            parts.append(str(imm))
        elif ot == OpType.FP_IMM16:
            lo = next(non_fp_iter)
            hi = next(non_fp_iter)
            parts.append(str(lo | (hi << 8)))
        else:
            val = next(non_fp_iter)
            parts.append(_fmt_operand(ot, val))

    # Determine suffix from first FPM byte
    if fp_decoded:
        first_fmt = fp_decoded[0][1]
        suffix = _FMT_TO_SUFFIX.get(first_fmt, f"?{first_fmt}")
        # FCVT: dual suffix if formats differ
        if len(fp_decoded) == 2 and fp_decoded[0][1] != fp_decoded[1][1]:
            dst_suf = _FMT_TO_SUFFIX.get(fp_decoded[0][1], "?")
            src_suf = _FMT_TO_SUFFIX.get(fp_decoded[1][1], "?")
            label = f"{mnemonic}.{dst_suf}.{src_suf}"
        else:
            label = f"{mnemonic}.{suffix}"
    else:
        label = mnemonic

    if parts:
        return f"{label} {', '.join(parts)}"
    return label


def disasm_insn(opcode: int, operands: tuple[int, ...] = ()) -> str:
    """Disassemble one instruction to text, e.g. 'MOV A, 42'."""
    defn = BY_CODE.get(opcode)
    if defn is not None:
        ops = [
            _fmt_operand(ot, val) for ot, val in zip(defn.sig, operands)
        ]
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
