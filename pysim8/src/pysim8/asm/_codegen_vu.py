"""VU instruction encoding helpers."""

from __future__ import annotations

from pysim8.asm._codegen_core import AssemblerError, _lookup_suffix
from pysim8.asm.parser import (
    OpAddr,
    OpAddrLabel,
    OpConst,
    Operand,
    OpLabel,
    OpPageLabel,
    OpReg,
    OpRegAddr,
    OpVuReg,
)
from pysim8.isa import (
    ISA_VU,
    VU_CMP_SUFFIX,
    VU_FMT_ELEM_SIZE,
    VU_MODE_R,
    VU_MODE_VI,
    VU_MODE_VS,
    VU_MODE_VV,
    VU_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_MODE,
    VU_SYNC_MNEMONICS,
    Op,
    encode_regaddr,
    encode_vfm,
    encode_vu_regs,
)

_VSET_BYTE_EXPR = (OpConst, OpLabel, OpPageLabel, OpAddrLabel)

_VU_MNEMONIC_TO_OP: dict[str, int] = {d.mnemonic: int(d.op) for d in ISA_VU if d.mnemonic not in VU_SYNC_MNEMONICS}
# VFILL is an alias for VMOV — emits opcode 182 (Op.VMOV) with forced vi mode
_VU_MNEMONIC_TO_OP["VFILL"] = int(Op.VMOV)

_VU_SINGLE_MODE: frozenset[str] = frozenset({"VDOT", "VSQRT", "VNEG", "VABS", "VSEL"})


def _encode_vu_instruction(
    mnemonic: str,
    operands: list[Operand],
    dst_suffix: str | None,
    src_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode one VU instruction into bytes."""
    if mnemonic in VU_SYNC_MNEMONICS:
        return _encode_vu_sync(mnemonic, operands, line)
    return _encode_vu_async(mnemonic, operands, dst_suffix, src_suffix, line)


def _encode_vu_sync(mnemonic: str, operands: list[Operand], line: int) -> list[int]:
    """Encode synchronous VU instruction."""
    if mnemonic == "VFCLR":
        return [int(Op.VFCLR)]
    if mnemonic == "VWAIT":
        return [int(Op.VWAIT)]
    if mnemonic == "VFSTAT":
        if len(operands) != 1 or not isinstance(operands[0], OpReg):
            raise AssemblerError("VFSTAT requires one GPR operand", line)
        if operands[0].code > 3:
            raise AssemblerError("VFSTAT requires GPR A-D", line)
        return [int(Op.VFSTAT), operands[0].code]
    if mnemonic == "VSET":
        return _encode_vset(operands, line)
    raise AssemblerError(f"Unknown VU sync instruction: {mnemonic}", line)


def _encode_vset(operands: list[Operand], line: int) -> list[int]:
    """Encode VSET instruction (4 forms: imm16, gpr-pair, mem, memi)."""
    if len(operands) < 2:
        raise AssemblerError("VSET requires at least 2 operands", line)
    if not isinstance(operands[0], OpVuReg):
        raise AssemblerError("VSET first operand must be a VU register", line)
    target = operands[0].code

    # VSET reg, rH, rL — GPR pair; must come before composite check
    if len(operands) == 3 and isinstance(operands[1], OpReg) and isinstance(operands[2], OpReg):
        rh, rl = operands[1].code, operands[2].code
        if rh > 3 or rl > 3:
            raise AssemblerError("VSET GPR pair requires A-D", line)
        return [int(Op.VSET_GPR), target, (rh << 2) | rl]

    # VSET reg, gpr — single GPR, zero-extended to 16-bit (bit 4 flag)
    if len(operands) == 2 and isinstance(operands[1], OpReg):
        gpr = operands[1].code
        if gpr > 3:
            raise AssemblerError("VSET single GPR requires A-D", line)
        return [int(Op.VSET_GPR), target, 0x10 | gpr]

    # VSET reg, hi, lo — composite byte-expression pair
    if len(operands) == 3 and isinstance(operands[1], _VSET_BYTE_EXPR) and isinstance(operands[2], _VSET_BYTE_EXPR):
        hi_val = operands[1].value if isinstance(operands[1], OpConst) else 0
        lo_val = operands[2].value if isinstance(operands[2], OpConst) else 0
        if isinstance(operands[1], OpConst) and not 0 <= hi_val <= 255:
            raise AssemblerError(f"VSET composite hi operand out of range: {hi_val}", line)
        if isinstance(operands[2], OpConst) and not 0 <= lo_val <= 255:
            raise AssemblerError(f"VSET composite lo operand out of range: {lo_val}", line)
        return [int(Op.VSET_IMM16), target, lo_val & 0xFF, hi_val & 0xFF]

    # VSET reg, imm16 — single numeric immediate, 0–65535
    if len(operands) == 2 and isinstance(operands[1], OpConst):
        val = operands[1].value
        if val < 0 or val > 65535:
            raise AssemblerError(f"VSET immediate must be 0-65535, got {val}", line)
        return [int(Op.VSET_IMM16), target, val & 0xFF, (val >> 8) & 0xFF]

    # VSET reg, label — full 16-bit address: lo=offset(label), hi=page(label)
    if len(operands) == 2 and isinstance(operands[1], OpLabel):
        return [int(Op.VSET_IMM16), target, 0, 0]

    # VSET reg, [addr] / [label] — read 16-bit LE from DP×256+addr
    if len(operands) == 2 and isinstance(operands[1], (OpAddr, OpAddrLabel)):
        addr = operands[1].value if isinstance(operands[1], OpAddr) else 0
        return [int(Op.VSET_MEM), target, addr]

    # VSET reg, [reg±offset]
    if len(operands) == 2 and isinstance(operands[1], OpRegAddr):
        return [int(Op.VSET_MEMI), target, encode_regaddr(operands[1].reg_code, operands[1].offset)]

    raise AssemblerError("VSET does not support this operand(s)", line)


def _resolve_vu_mode_cond(
    mnemonic: str,
    mode_suffix: str | None,
    operands: list[Operand],
    line: int,
) -> tuple[int, int]:
    """Resolve VU mode and condition from mnemonic, suffix, and operands."""
    if mnemonic == "VCMP":
        if mode_suffix is None:
            raise AssemblerError("VCMP requires a condition suffix", line)
        return 0, _lookup_suffix(mode_suffix, VU_CMP_SUFFIX, "Invalid VCMP condition", line)
    if mnemonic == "VFILL":
        return VU_MODE_VI, 0
    if mnemonic in _VU_SINGLE_MODE:
        return 0, 0
    if mode_suffix is not None:
        return _lookup_suffix(mode_suffix, VU_SUFFIX_TO_MODE, "Invalid VU mode suffix", line), 0
    non_vu = [op for op in operands if not isinstance(op, OpVuReg)]
    has_gpr = any(isinstance(op, OpReg) for op in non_vu)
    has_imm = any(isinstance(op, OpConst) for op in non_vu)
    vu_count = sum(1 for op in operands if isinstance(op, OpVuReg))
    if has_gpr:
        return VU_MODE_VS, 0
    if has_imm:
        return VU_MODE_VI, 0
    if vu_count <= 2:
        return VU_MODE_R, 0
    return VU_MODE_VV, 0


def _resolve_vu_fmt(mnemonic: str, fmt_suffix: str | None, line: int) -> int:
    """Validate and resolve VU format suffix to fmt code."""
    if fmt_suffix is None:
        raise AssemblerError(f"{mnemonic} requires a format suffix", line)
    return _lookup_suffix(fmt_suffix, VU_SUFFIX_TO_FMT, "Invalid VU format suffix", line)


def _encode_vu_regs_from_operands(operands: list[Operand], mnemonic: str, mode: int, line: int) -> int:
    """Extract and validate VU pointer registers from operands, return encoded byte."""
    vu_regs = [op for op in operands if isinstance(op, OpVuReg)]
    if not vu_regs:
        raise AssemblerError(f"{mnemonic} requires VU register operands", line)
    for r in vu_regs:
        if r.code > 3:
            raise AssemblerError("Async VU operands must be pointer registers (VA-VM)", line)
    dc = vu_regs[0].code
    s1c = vu_regs[1].code if len(vu_regs) > 1 else 0
    if mode == VU_MODE_VS:
        gpr_ops = [op for op in operands if isinstance(op, OpReg)]
        if not gpr_ops:
            raise AssemblerError(f"{mnemonic} broadcast requires a GPR operand (A-D)", line)
        gpr_code = gpr_ops[0].code
        if gpr_code > 3:
            raise AssemblerError("Broadcast GPR must be A-D", line)
        s2c = gpr_code
    else:
        s2c = vu_regs[2].code if len(vu_regs) > 2 else 0
    return encode_vu_regs(dc, s1c, s2c)


def _encode_vu_async(
    mnemonic: str,
    operands: list[Operand],
    fmt_suffix: str | None,
    mode_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode asynchronous VU instruction."""
    opcode = _VU_MNEMONIC_TO_OP.get(mnemonic)
    if opcode is None:
        raise AssemblerError(f"Unknown VU async instruction: {mnemonic}", line)

    fmt = _resolve_vu_fmt(mnemonic, fmt_suffix, line)
    mode, cond = _resolve_vu_mode_cond(mnemonic, mode_suffix, operands, line)

    if mode == VU_MODE_VS and VU_FMT_ELEM_SIZE.get(fmt, 1) > 1:
        raise AssemblerError(f"GPR broadcast only for byte formats (U/I/O3/O2), not .{fmt_suffix}", line)

    regs_byte = _encode_vu_regs_from_operands(operands, mnemonic, mode, line)
    encoded = [opcode, encode_vfm(fmt, mode), regs_byte]

    if mnemonic == "VCMP":
        encoded.append(cond)

    if mode == VU_MODE_VI:
        imm_ops = [op for op in operands if isinstance(op, OpConst)]
        if not imm_ops:
            raise AssemblerError(f"{mnemonic} requires an immediate operand", line)
        imm_val = imm_ops[0].value
        elem_sz = VU_FMT_ELEM_SIZE.get(fmt, 1)
        for i in range(elem_sz):
            encoded.append((imm_val >> (8 * i)) & 0xFF)

    return encoded
