"""Disassembler core: decode machine code back to assembly text."""

from __future__ import annotations

from collections.abc import Mapping

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
    BY_CODE_VU,
    FP_CONTROL_MNEMONICS,
    FP_FMT_BF,
    FP_FMT_F,
    FP_FMT_H,
    FP_FMT_O3,
    FP_REGISTERS,
    FP_SUFFIX_TO_FMT,
    VU_ASYNC_OPS,
    VU_CMP_SUFFIX,
    VU_REGISTERS,
    VU_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_MODE,
    FpRegInfo,
    Op,
    OpType,
    Reg,
    decode_fpm,
    decode_regaddr,
    decode_vfm,
    decode_vu_regs,
    vu_instr_size,
)

__all__ = ["disasm_instr", "disasm"]

_REG_NAMES: dict[int, str] = {r.value: r.name for r in Reg}


def _lookup_instr_def(opcode: int) -> object:
    """Look up an InstrDef by opcode across all ISA tables."""
    return BY_CODE.get(opcode) or BY_CODE_FP.get(opcode) or BY_CODE_VU.get(opcode)


def _build_fpm_to_reg(
    regs: Mapping[str, FpRegInfo],
) -> dict[tuple[int, int, int], str]:
    """Build reverse lookup: (phys, pos, fmt) → shortest register name."""
    result: dict[tuple[int, int, int], str] = {}
    for name, r in regs.items():
        key = (r.phys, r.pos, r.fmt)
        if key not in result or len(name) < len(result[key]):
            result[key] = name
    return result


_FPM_TO_REG = _build_fpm_to_reg(FP_REGISTERS)

# fmt code → shortest suffix name (derived from ISA's FP_SUFFIX_TO_FMT)
_FMT_TO_SUFFIX: dict[int, str] = {}
for _name, _code in FP_SUFFIX_TO_FMT.items():
    if _code not in _FMT_TO_SUFFIX or len(_name) < len(_FMT_TO_SUFFIX[_code]):
        _FMT_TO_SUFFIX[_code] = _name


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


def _disasm_fp_instr(opcode: int, raw_operands: tuple[int, ...]) -> str | None:
    """Disassemble one FP instruction. Returns None if opcode not FP."""
    instr_def = BY_CODE_FP.get(opcode)
    if instr_def is None:
        return None

    mnemonic = instr_def.mnemonic
    if mnemonic in FP_CONTROL_MNEMONICS:
        parts = [_fmt_operand(ot, val) for ot, val in zip(instr_def.format, raw_operands)]
        return f"{mnemonic} {', '.join(parts)}" if parts else mnemonic

    fp_count = sum(1 for ot in instr_def.format if ot == OpType.FP_REG)
    fp_decoded: list[tuple[str, int]] = [_fmt_fpm(b) for b in raw_operands[:fp_count]]
    fp_iter = iter(fp_decoded)
    non_fp_iter = iter(raw_operands[fp_count:])
    fmt_code = -1
    parts = []

    for ot in instr_def.format:
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


# ── VU helpers ────────────────────────────────────────────────────

_VU_REG_NAMES: dict[int, str] = {v: k for k, v in VU_REGISTERS.items() if k != "VL"}
_VU_REG_NAMES[4] = "VL"

_VU_FMT_TO_SUFFIX: dict[int, str] = {}
for _name, _code in VU_SUFFIX_TO_FMT.items():
    if _code not in _VU_FMT_TO_SUFFIX or len(_name) < len(_VU_FMT_TO_SUFFIX[_code]):
        _VU_FMT_TO_SUFFIX[_code] = _name

_VU_MODE_TO_SUFFIX: dict[int, str] = {v: k.lower() for k, v in VU_SUFFIX_TO_MODE.items()}

_VU_COND_TO_SUFFIX: dict[int, str] = {v: k for k, v in VU_CMP_SUFFIX.items()}

# Instructions with no mode suffix (single valid mode)
_VU_SINGLE_MODE = frozenset({"VDOT", "VSQRT", "VNEG", "VABS", "VSEL", "VMOV", "VFILL", "VGATHER", "VSCATTER"})
# Instructions with only dst, src1 operands
_VU_DST_SRC1_ONLY = frozenset({"VSQRT", "VNEG", "VABS", "VMOV", "VGATHER", "VSCATTER"})


def _disasm_vu_sync(opcode: int, raw: tuple[int, ...]) -> str | None:
    """Disassemble a synchronous VU instruction."""
    instr_def = BY_CODE_VU.get(opcode)
    if instr_def is None:
        return None
    if opcode == Op.VFCLR:
        return "VFCLR"
    if opcode == Op.VWAIT:
        return "VWAIT"
    if opcode == Op.VFSTAT:
        return f"VFSTAT {_REG_NAMES.get(raw[0], '?')}"
    # VSET variants
    target = _VU_REG_NAMES.get(raw[0], f"?{raw[0]}")
    if opcode == Op.VSET_IMM16:
        val = raw[1] | (raw[2] << 8)
        return f"VSET {target}, {val:#06x}"
    if opcode == Op.VSET_GPR:
        rh = (raw[1] >> 2) & 0x03
        rl = raw[1] & 0x03
        return f"VSET {target}, {_REG_NAMES.get(rh, '?')}, {_REG_NAMES.get(rl, '?')}"
    if opcode == Op.VSET_MEM:
        return f"VSET {target}, [{raw[1]}]"
    if opcode == Op.VSET_MEMI:
        return f"VSET {target}, {_fmt_regaddr(raw[1])}"
    return None


def _disasm_vu_async(opcode: int, code: bytes | list[int], offset: int) -> tuple[str, int] | None:
    """Disassemble an async VU instruction. Returns (text, size) or None."""
    if opcode not in VU_ASYNC_OPS:
        return None
    instr_def = BY_CODE_VU.get(opcode)
    if instr_def is None:
        return None
    if offset + 3 > len(code):
        return None
    vfm_enc = code[offset + 1]
    regs = code[offset + 2]
    fmt, mode, cond = decode_vfm(vfm_enc)
    dst, src1, src2 = decode_vu_regs(regs)
    size = vu_instr_size(opcode, vfm_enc)
    if offset + size > len(code):
        return None

    mnemonic = instr_def.mnemonic
    suffix = _VU_FMT_TO_SUFFIX.get(fmt, f"?{fmt}")
    dn = _VU_REG_NAMES.get(dst, f"?{dst}")
    s1n = _VU_REG_NAMES.get(src1, f"?{src1}")
    s2n = _VU_REG_NAMES.get(src2, f"?{src2}")

    # Label: MNEMONIC.fmt[.cond] — no mode suffix (inferred from operands)
    if mnemonic == "VCMP":
        label = f"{mnemonic}.{suffix}.{_VU_COND_TO_SUFFIX.get(cond, f'?{cond}')}"
    else:
        label = f"{mnemonic}.{suffix}"

    # Operands — mode determines src2 display
    if mnemonic in _VU_DST_SRC1_ONLY:
        parts = f"{dn}, {s1n}"
    elif mnemonic == "VFILL" or mode == 2:  # immediate
        imm_bytes = code[offset + 3 : offset + size]
        imm = int.from_bytes(imm_bytes, "little") if imm_bytes else 0
        parts = f"{dn}, {imm}" if mnemonic == "VFILL" else f"{dn}, {s1n}, {imm}"
    elif mode == 1:  # GPR broadcast
        gpr_name = _REG_NAMES.get(src2, f"?{src2}")
        parts = f"{dn}, {s1n}, {gpr_name}"
    elif mode == 3:  # reduction
        parts = f"{dn}, {s1n}"
    else:  # .vv
        parts = f"{dn}, {s1n}, {s2n}"

    return f"{label} {parts}", size


def disasm_instr(opcode: int, operands: tuple[int, ...] = ()) -> str:
    """Disassemble one instruction to text, e.g. 'MOV A, 42'."""
    instr_def = BY_CODE.get(opcode)
    if instr_def is not None:
        ops = [_fmt_operand(ot, val) for ot, val in zip(instr_def.format, operands)]
        if ops:
            return f"{instr_def.mnemonic} {', '.join(ops)}"
        return instr_def.mnemonic

    # Try FP instruction
    result = _disasm_fp_instr(opcode, operands)
    if result is not None:
        return result

    # Try VU sync instruction
    vu_result = _disasm_vu_sync(opcode, operands)
    if vu_result is not None:
        return vu_result

    # Try VU async instruction (reconstruct code bytes)
    if opcode in VU_ASYNC_OPS:
        buf = bytes([opcode, *operands])
        vu = _disasm_vu_async(opcode, buf, 0)
        if vu is not None:
            return vu[0]

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

        # Try async VU first (variable-size, needs raw code access)
        if opcode in VU_ASYNC_OPS:
            vu = _disasm_vu_async(opcode, code, i)
            if vu is not None:
                text, size = vu
                result.append((i, text, size))
                i += size
                continue

        instr_def = _lookup_instr_def(opcode)
        if instr_def is None:
            result.append((i, f"DB {opcode}", 1))
            i += 1
            continue
        size = instr_def.size
        if i + size > len(code):
            result.append((i, f"DB {opcode}", 1))
            i += 1
            continue
        operands = tuple(code[i + k] for k in range(1, size))
        result.append((i, disasm_instr(opcode, operands), size))
        i += size
    return result
