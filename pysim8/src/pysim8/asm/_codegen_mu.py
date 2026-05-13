"""MU instruction encoding helpers."""

from __future__ import annotations

from pysim8.asm._codegen_core import AssemblerError, _lookup_suffix
from pysim8.asm.parser import (
    OpAddr,
    OpAddrLabel,
    OpConst,
    Operand,
    OpLabel,
    OpMuReg,
    OpPageLabel,
    OpReg,
    OpRegAddr,
)
from pysim8.isa import (
    ISA_MU,
    MU_SUFFIX_TO_FMT,
    MU_SYNC_MNEMONICS,
    Op,
    encode_mfm,
    encode_vu_regs,
)

_MSET_BYTE_EXPR = (OpConst, OpLabel, OpPageLabel, OpAddrLabel)

_MU_MNEMONIC_TO_OP: dict[str, int] = {d.mnemonic: int(d.op) for d in ISA_MU if d.mnemonic not in MU_SYNC_MNEMONICS}

# MM=3, MN=4, MK=5
_SHAPE_REG_CODES = (3, 4, 5)


def _encode_mu_instruction(
    mnemonic: str,
    operands: list[Operand],
    dst_suffix: str | None,
    src_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode one MU instruction into bytes."""
    if mnemonic in MU_SYNC_MNEMONICS:
        return _encode_mu_sync(mnemonic, operands, line)
    return _encode_mu_async(mnemonic, operands, dst_suffix, src_suffix, line)


def _encode_mshape(operands: list[Operand], line: int) -> list[int]:
    """Encode MSHAPE M, N, K → MSET MM, M; MSET MN, N; MSET MK, K."""
    if len(operands) != 3:
        raise AssemblerError("MSHAPE requires three immediates: M, N, K", line)
    out: list[int] = []
    for reg_code, op in zip(_SHAPE_REG_CODES, operands):
        if not isinstance(op, OpConst):
            raise AssemblerError("MSHAPE operands must be numeric immediates", line)
        val = op.value
        if not 0 <= val <= 65535:
            raise AssemblerError(f"MSHAPE dimension out of range: {val}", line)
        out += [int(Op.MSET_IMM16), reg_code, val & 0xFF, (val >> 8) & 0xFF]
    return out


def _encode_mu_sync(mnemonic: str, operands: list[Operand], line: int) -> list[int]:
    """Encode synchronous MU instruction."""
    if mnemonic == "MSHAPE":
        return _encode_mshape(operands, line)
    if mnemonic == "MFCLR":
        return [int(Op.MFCLR)]
    if mnemonic == "MWAIT":
        return [int(Op.MWAIT)]
    if mnemonic == "MFSTAT":
        if len(operands) != 1 or not isinstance(operands[0], OpReg):
            raise AssemblerError("MFSTAT requires one GPR operand", line)
        if operands[0].code > 3:
            raise AssemblerError("MFSTAT requires GPR A-D", line)
        return [int(Op.MFSTAT), operands[0].code]
    if mnemonic == "MSET":
        return _encode_mset(operands, line)
    raise AssemblerError(f"Unknown MU sync instruction: {mnemonic}", line)


def _encode_mset(operands: list[Operand], line: int) -> list[int]:
    """Encode MSET instruction (variants: imm16, gpr-pair, single GPR)."""
    if len(operands) < 2:
        raise AssemblerError("MSET requires at least 2 operands", line)
    if not isinstance(operands[0], OpMuReg):
        raise AssemblerError("MSET first operand must be an MU register", line)
    target = operands[0].code

    # MSET reg, rH, rL — GPR pair
    if len(operands) == 3 and isinstance(operands[1], OpReg) and isinstance(operands[2], OpReg):
        rh, rl = operands[1].code, operands[2].code
        if rh > 3 or rl > 3:
            raise AssemblerError("MSET GPR pair requires A-D", line)
        return [int(Op.MSET_GPR), target, (rh << 2) | rl]

    # MSET reg, gpr — single GPR
    if len(operands) == 2 and isinstance(operands[1], OpReg):
        gpr = operands[1].code
        if gpr > 3:
            raise AssemblerError("MSET single GPR requires A-D", line)
        return [int(Op.MSET_GPR), target, 0x10 | gpr]

    # MSET reg, hi, lo — composite byte-expression pair
    if len(operands) == 3 and isinstance(operands[1], _MSET_BYTE_EXPR) and isinstance(operands[2], _MSET_BYTE_EXPR):
        hi_val = operands[1].value if isinstance(operands[1], OpConst) else 0
        lo_val = operands[2].value if isinstance(operands[2], OpConst) else 0
        if isinstance(operands[1], OpConst) and not 0 <= hi_val <= 255:
            raise AssemblerError(f"MSET composite hi out of range: {hi_val}", line)
        if isinstance(operands[2], OpConst) and not 0 <= lo_val <= 255:
            raise AssemblerError(f"MSET composite lo out of range: {lo_val}", line)
        return [int(Op.MSET_IMM16), target, lo_val & 0xFF, hi_val & 0xFF]

    # MSET reg, imm16 — single numeric immediate
    if len(operands) == 2 and isinstance(operands[1], OpConst):
        val = operands[1].value
        if val < 0 or val > 65535:
            raise AssemblerError(f"MSET immediate must be 0-65535, got {val}", line)
        return [int(Op.MSET_IMM16), target, val & 0xFF, (val >> 8) & 0xFF]

    # MSET reg, label
    if len(operands) == 2 and isinstance(operands[1], OpLabel):
        return [int(Op.MSET_IMM16), target, 0, 0]

    # MSET reg, [addr] / [reg] — not supported in initial MU release
    if len(operands) == 2 and isinstance(operands[1], (OpAddr, OpAddrLabel, OpRegAddr)):
        raise AssemblerError("MSET memory-operand variant not yet supported", line)

    raise AssemblerError("MSET does not support these operands", line)


def _resolve_mu_fmt(mnemonic: str, fmt_suffix: str | None, line: int) -> int:
    if fmt_suffix is None:
        raise AssemblerError(f"{mnemonic} requires a format suffix", line)
    return _lookup_suffix(fmt_suffix, MU_SUFFIX_TO_FMT, "Invalid MU format suffix", line)


def _resolve_mu_layout(extra_suffix: str | None, line: int) -> tuple[bool, bool, bool]:
    """Parse optional layout suffix: 3 chars r/c for A, B, C matrices.

    Accepts None or a 3-char string like 'rrr', 'rcr', 'ccc', etc.
    Defaults to row-major for all (False, False, False).
    """
    if extra_suffix is None:
        return False, False, False
    layout = extra_suffix.strip().lower()
    if len(layout) != 3 or not all(c in "rc" for c in layout):
        raise AssemblerError(
            f"Invalid layout suffix '.{extra_suffix}'; expected 3 chars r/c (e.g. '.rrr', '.rcr')",
            line,
        )
    return layout[0] == "c", layout[1] == "c", layout[2] == "c"


def _encode_mu_async(
    mnemonic: str,
    operands: list[Operand],
    fmt_suffix: str | None,
    extra_suffix: str | None,
    line: int,
) -> list[int]:
    """Encode async MU instruction (MMUL or MMAD)."""
    opcode = _MU_MNEMONIC_TO_OP.get(mnemonic)
    if opcode is None:
        raise AssemblerError(f"Unknown MU async instruction: {mnemonic}", line)

    fmt = _resolve_mu_fmt(mnemonic, fmt_suffix, line)
    a_col, b_col, c_col = _resolve_mu_layout(extra_suffix, line)

    mu_regs = [op for op in operands if isinstance(op, OpMuReg)]
    if len(mu_regs) != 3:
        raise AssemblerError(f"{mnemonic} requires three MU pointer operands (MC, MA, MB)", line)
    for r in mu_regs:
        if r.code > 2:
            raise AssemblerError(f"{mnemonic} operands must be MA/MB/MC (codes 0–2)", line)
    dc, s1c, s2c = mu_regs[0].code, mu_regs[1].code, mu_regs[2].code
    return [opcode, encode_mfm(fmt, a_col, b_col, c_col), encode_vu_regs(dc, s1c, s2c)]
