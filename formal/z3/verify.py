"""Z3 formal verification of sim8 ISA encoding schemes.

Proves correctness of the four byte-packing encodings defined in spec/isa.json
using Z3 SMT solver, then cross-checks the JSON data for structural consistency.

Usage:
    uv run verify.py           # from formal/z3/
    uv run verify.py --quiet   # suppress [PROVED] lines, show only failures

Proof obligations:
    REGADDR  — roundtrip, injectivity, output-fits-byte, reg-field preserved,
               right-inverse: encode(decode(b)) == b (universal),
               DP (code 5) outside valid domain
    FPM      — roundtrip, injectivity, structural bound (byte ≤ 0x7E),
               right-inverse: encode(decode(b)) == b (universal),
               30 named registers have distinct bytes
    VFM      — roundtrip, injectivity, upper-3-bits always zero,
               left-inverse: encode(decode(b)) == b & 0x1F
    VU_REGS  — roundtrip, injectivity, lower-2-bits always zero,
               left-inverse: encode(decode(b)) == b & 0xFC

Data checks (isa.json consistency):
    D1   opcode uniqueness across all tables
    D2   opcode ranges: core 0-127, FP 128-162, VU 163-183
    D3   VU format codes 0-6 in order
    D4   VU mode codes 0-3 in order
    D5   VU condition codes 0-5 in order
    D6   FP register FPM bytes are distinct
    D7   FP register (pos, fmt) validity per FP_FMT_MAX_POS
    D8   FP format widths match constants
    D9   VU elem_size matches constants
    D10  Instruction size calculation in [1,4] (current max; spec reserves up to 7)
    D11  Every VU instruction is sync or async, exactly 7 sync
    D12  FP format codes 0-6 in order; max_pos matches constants
    D13  since field: core=1, FP=2, VU=3
    D14  All operand types from the known set
    D15  All instruction costs ≥ 0
    D16  VU operand structure: async binary=2, VCMP=3, sync per fixed table
    D17  Mnemonic aliases resolve to existing mnemonics
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import z3

# ── Paths ─────────────────────────────────────────────────────────────────────

_REPO = Path(__file__).parent.parent.parent
_ISA_JSON = _REPO / "spec" / "isa.json"

# ── ISA constants (mirrors pysim8/src/pysim8/constants.py) ────────────────────

_FP_FMT_MAX_POS = {0: 0, 1: 1, 2: 1, 3: 3, 4: 3, 5: 7, 6: 7}
_FP_FMT_WIDTH = {0: 32, 1: 16, 2: 16, 3: 8, 4: 8, 5: 4, 6: 4}
_VU_FMT_ELEM_SIZE = {0: 4, 1: 2, 2: 2, 3: 1, 4: 1, 5: 1, 6: 1}
_OP_BYTES = {"fp_imm16": 2}  # operand types wider than 1 byte

_RA_OFF_MAX: int = 15  # max positive offset in regaddr (5-bit signed)
_RA_OFF_RANGE: int = 32  # 2^5, used for two's-complement wrap

_KNOWN_OPERAND_TYPES = frozenset(
    {
        "reg",
        "reg_arith",
        "reg_gpr",
        "reg_stack",
        "imm",
        "mem",
        "regaddr",
        "fp_reg",
        "fp_imm8",
        "fp_imm16",
    }
)

# Sync VU instruction → expected operand list (spec/vector.md)
_VU_SYNC_OPERANDS: dict[str, list[str]] = {
    "VFCLR": [],
    "VWAIT": [],
    "VFSTAT": ["imm"],
    "VSET_GPR": ["imm", "imm"],
    "VSET_MEM": ["imm", "imm"],
    "VSET_MEMI": ["imm", "imm"],
    "VSET_IMM16": ["imm", "fp_imm16"],
}


def _fpm_byte(r: dict[str, int]) -> int:
    return (r["phys"] << 6) | (r["pos"] << 3) | r["fmt"]


def _isize(i: dict[str, Any]) -> int:
    return 1 + sum(_OP_BYTES.get(op, 1) for op in i["operands"])


# ── Proof harness ─────────────────────────────────────────────────────────────

_quiet = False
_failures: list[str] = []
_passed: int = 0


def _ok(label: str) -> None:
    global _passed
    _passed += 1
    if not _quiet:
        print(f"  [PROVED] {label}")


def _fail(label: str, model: z3.ModelRef | None = None) -> None:
    msg = f"  [FAIL]   {label}"
    if model is not None:
        msg += f"\n           counterexample: {model}"
    print(msg)
    _failures.append(label)


def prove(claim: z3.BoolRef, *hypotheses: z3.BoolRef, label: str) -> bool:
    """Try to prove `claim` holds under `hypotheses`. Returns True if proved."""
    s = z3.Solver()
    s.add(*hypotheses)
    s.add(z3.Not(claim))
    result = s.check()
    if result == z3.unsat:
        _ok(label)
        return True
    model = s.model() if result == z3.sat else None
    _fail(label, model)
    return False


def check(condition: bool, label: str) -> bool:
    """Assert a Python-level invariant."""
    if condition:
        _ok(label)
        return True
    _fail(label)
    return False


# ── REGADDR encoding ──────────────────────────────────────────────────────────
#
# Bit layout (8-bit byte):
#   bits [7:3] = offset_unsigned  (5-bit two's-complement of offset ∈ [-16,+15])
#   bits [2:0] = reg_code         (3-bit, valid range 0..4; codes 5-7 → FAULT)
#
# encode(reg, off):  off_u = off if off ≥ 0 else 32 + off
#                    byte  = (off_u << 3) | reg
# decode(byte):      reg   = byte & 0x07
#                    off_u = byte >> 3
#                    off   = off_u if off_u ≤ 15 else off_u - 32
#
# Algebraic identity: encode(decode(b)) = b  for all b  (right-inverse)


def _z3_encode_regaddr(reg: z3.BitVecRef, off: z3.BitVecRef) -> z3.BitVecRef:
    """reg: BitVec(8), off: BitVec(8) signed — returns BitVec(8)."""
    off_u = z3.If(off >= 0, off, _RA_OFF_RANGE + off)
    return (off_u << 3) | reg


def _z3_decode_regaddr(byte: z3.BitVecRef) -> tuple[z3.BitVecRef, z3.BitVecRef]:
    """Returns (reg: BitVec(8), off: BitVec(8) signed)."""
    reg = byte & 0x07
    off_u = z3.LShR(byte, 3)
    off = z3.If(z3.ULE(off_u, _RA_OFF_MAX), off_u, off_u - _RA_OFF_RANGE)
    return reg, off


def verify_regaddr() -> None:
    print("REGADDR encoding")
    reg = z3.BitVec("reg", 8)
    off = z3.BitVec("off", 8)

    # Valid regaddr register codes: 0=A, 1=B, 2=C, 3=D, 4=SP.
    # Code 5 (DP) and codes 6-7 are not valid in regaddr — they trigger
    # FAULT(ERR_INVALID_REG) at runtime (spec/isa.md §1.4).
    valid = z3.And(z3.ULE(reg, 4), off >= -16, off <= 15)

    enc = _z3_encode_regaddr(reg, off)
    dec_reg, dec_off = _z3_decode_regaddr(enc)

    prove(dec_reg == reg, valid, label="roundtrip: decoded reg == original reg")
    prove(dec_off == off, valid, label="roundtrip: decoded off == original off")

    # Injectivity: distinct valid inputs encode to distinct bytes
    reg2 = z3.BitVec("reg2", 8)
    off2 = z3.BitVec("off2", 8)
    valid2 = z3.And(z3.ULE(reg2, 4), off2 >= -16, off2 <= 15)
    enc2 = _z3_encode_regaddr(reg2, off2)
    distinct_inputs = z3.Or(reg != reg2, off != off2)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct_inputs,
        label="injectivity: distinct inputs → distinct bytes",
    )

    # DP (code 5) is outside the valid regaddr domain → fault at runtime
    dp_code = z3.BitVecVal(5, 8)
    prove(
        z3.UGT(dp_code, z3.BitVecVal(4, 8)),
        label="DP (code 5) is outside valid regaddr domain (causes FAULT)",
    )

    # Output fits in 8 bits
    prove(z3.ULE(enc, 255), valid, label="output is a valid byte")

    # Reg field in encoded byte is preserved (no bleed from offset)
    prove((enc & 0x07) == reg, valid, label="encoded byte[2:0] == reg")

    # Right-inverse: encode(decode(b)) = b  for ALL bytes (no constraints)
    b = z3.BitVec("b_ra", 8)
    d_reg, d_off = _z3_decode_regaddr(b)
    prove(
        _z3_encode_regaddr(d_reg, d_off) == b,
        label="right-inverse: encode(decode(b)) == b (universal)",
    )
    print()


# ── FPM encoding ──────────────────────────────────────────────────────────────
#
# Bit layout (8-bit byte):
#   bits [7:6] = phys  (2-bit, valid 0..1)
#   bits [5:3] = pos   (3-bit, valid 0..FP_FMT_MAX_POS[fmt])
#   bits [2:0] = fmt   (3-bit, valid 0..6; fmt 5-6 are N1/N2 reserved formats)
#
# encode(phys, pos, fmt): (phys << 6) | (pos << 3) | fmt
# decode(byte):           phys = byte[7:6] & 3,  pos = byte[5:3] & 7,  fmt = byte & 7
#
# Algebraic identity: encode(decode(b)) = b  for all b  (right-inverse)
# Structural bound:   valid byte ≤ 0x7E  (phys ≤ 1 → bit 7 always 0)


def _z3_encode_fpm(
    phys: z3.BitVecRef, pos: z3.BitVecRef, fmt: z3.BitVecRef
) -> z3.BitVecRef:
    """All args BitVec(8) — returns BitVec(8)."""
    return (phys << 6) | (pos << 3) | fmt


def _z3_decode_fpm(
    byte: z3.BitVecRef,
) -> tuple[z3.BitVecRef, z3.BitVecRef, z3.BitVecRef]:
    """Returns (phys, pos, fmt) each BitVec(8)."""
    phys = z3.LShR(byte, 6) & 0x03
    pos = z3.LShR(byte, 3) & 0x07
    fmt = byte & 0x07
    return phys, pos, fmt


def _z3_fpm_max_pos(fmt: z3.BitVecRef) -> z3.BitVecRef:
    """FP_FMT_MAX_POS as a Z3 If-chain covering all 7 formats (0..6).

    fmt 0     → max_pos 0
    fmt 1-2   → max_pos 1
    fmt 3-4   → max_pos 3
    fmt 5-6   → max_pos 7  (N1/N2 reserved formats)
    """
    return z3.If(
        fmt == 0,
        z3.BitVecVal(0, 8),
        z3.If(
            z3.ULE(fmt, 2),
            z3.BitVecVal(1, 8),
            z3.If(
                z3.ULE(fmt, 4),
                z3.BitVecVal(3, 8),
                z3.BitVecVal(7, 8),
            ),
        ),
    )


def verify_fpm(isa: dict[str, Any]) -> None:
    print("FPM encoding")
    phys = z3.BitVec("phys", 8)
    pos = z3.BitVec("pos", 8)
    fmt = z3.BitVec("fmt", 8)

    max_pos = _z3_fpm_max_pos(fmt)
    # Full valid domain: phys ∈ {0,1}, fmt ∈ {0..6}, pos ≤ max_pos[fmt]
    valid = z3.And(z3.ULE(phys, 1), z3.ULE(fmt, 6), z3.ULE(pos, max_pos))

    enc = _z3_encode_fpm(phys, pos, fmt)
    d_phys, d_pos, d_fmt = _z3_decode_fpm(enc)

    prove(d_phys == phys, valid, label="roundtrip: decoded phys == original phys")
    prove(d_pos == pos, valid, label="roundtrip: decoded pos == original pos")
    prove(d_fmt == fmt, valid, label="roundtrip: decoded fmt == original fmt")

    phys2 = z3.BitVec("phys2", 8)
    pos2 = z3.BitVec("pos2", 8)
    fmt2 = z3.BitVec("fmt2", 8)
    valid2 = z3.And(
        z3.ULE(phys2, 1), z3.ULE(fmt2, 6), z3.ULE(pos2, _z3_fpm_max_pos(fmt2))
    )
    enc2 = _z3_encode_fpm(phys2, pos2, fmt2)
    distinct = z3.Or(phys != phys2, pos != pos2, fmt != fmt2)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct,
        label="injectivity: distinct valid inputs → distinct bytes",
    )

    # Structural bound: phys ≤ 1 → bit 7 always 0; max byte = 0x7E (phys=1,pos=7,fmt=6)
    prove(
        z3.ULE(enc, 0x7E),
        valid,
        label="structural bound: valid FPM byte ≤ 0x7E (bit 7 always 0)",
    )

    # Right-inverse: encode(decode(b)) = b  for ALL bytes (no constraints needed)
    # Proof: (phys<<6)|(pos<<3)|fmt = (b&0xC0)|(b&0x38)|(b&0x07) = b & 0xFF = b
    b = z3.BitVec("b_fpm", 8)
    d_p, d_pos_b, d_f = _z3_decode_fpm(b)
    prove(
        _z3_encode_fpm(d_p, d_pos_b, d_f) == b,
        label="right-inverse: encode(decode(b)) == b (universal)",
    )

    # Data check: all 30 named FP registers produce distinct FPM bytes
    reg_bytes = [_fpm_byte(r) for r in isa["fp_registers"]]
    check(
        len(set(reg_bytes)) == len(reg_bytes),
        f"all {len(reg_bytes)} named FP registers have distinct FPM bytes",
    )

    n_reserved = sum(1 for r in isa["fp_registers"] if r["fmt"] >= 5)
    n_v2_valid = sum(1 for r in isa["fp_registers"] if r["fmt"] <= 4)
    check(
        n_reserved > 0,
        f"N1/N2 registers exist in isa.json ({n_reserved} entries, fmt≥5, reserved in v2)",
    )
    check(
        n_v2_valid == 14,
        f"exactly 14 v2-valid named FP registers (phys 0-1, fmt 0-4); got {n_v2_valid}",
    )
    print()


# ── VFM encoding ──────────────────────────────────────────────────────────────
#
# Bit layout (8-bit byte, upper 3 bits unused/zero):
#   bits [7:5] = 0    (reserved, always zero)
#   bits [4:3] = mode (2-bit, valid 0..3)
#   bits [2:0] = fmt  (3-bit, valid 0..6)
#
# encode(fmt, mode): (mode << 3) | fmt
# decode(byte):      fmt = byte & 0x07,  mode = (byte >> 3) & 0x03
#   Note: cond is NOT stored in the VFM byte; it is a separate byte in VCMP.
#
# Algebraic identity: encode(decode(b)) = b & 0x1F  (left-inverse)


def _z3_encode_vfm(fmt: z3.BitVecRef, mode: z3.BitVecRef) -> z3.BitVecRef:
    return (mode << 3) | fmt


def _z3_decode_vfm(byte: z3.BitVecRef) -> tuple[z3.BitVecRef, z3.BitVecRef]:
    """Returns (fmt, mode) — cond is always 0, not stored in byte."""
    fmt = byte & 0x07
    mode = z3.LShR(byte, 3) & 0x03
    return fmt, mode


def verify_vfm() -> None:
    print("VFM encoding")
    fmt = z3.BitVec("fmt", 8)
    mode = z3.BitVec("mode", 8)

    valid = z3.And(z3.ULE(fmt, 6), z3.ULE(mode, 3))

    enc = _z3_encode_vfm(fmt, mode)
    d_fmt, d_mode = _z3_decode_vfm(enc)

    prove(d_fmt == fmt, valid, label="roundtrip: decoded fmt == original fmt")
    prove(d_mode == mode, valid, label="roundtrip: decoded mode == original mode")

    fmt2 = z3.BitVec("fmt2", 8)
    mode2 = z3.BitVec("mode2", 8)
    valid2 = z3.And(z3.ULE(fmt2, 6), z3.ULE(mode2, 3))
    enc2 = _z3_encode_vfm(fmt2, mode2)
    distinct = z3.Or(fmt != fmt2, mode != mode2)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct,
        label="injectivity: distinct valid inputs → distinct bytes",
    )

    # Upper 3 bits are always zero in a valid VFM byte
    prove(z3.ULE(enc, 0x1F), valid, label="upper 3 bits always zero (byte ≤ 0x1F)")

    # Left-inverse: encode(decode(b)) = b & 0x1F  for all b (universal)
    byte = z3.BitVec("byte_vfm", 8)
    d_f, d_m = _z3_decode_vfm(byte)
    prove(
        _z3_encode_vfm(d_f, d_m) == (byte & 0x1F),
        label="left-inverse: encode(decode(b)) == b & 0x1F (universal)",
    )
    print()


# ── VU_REGS encoding ──────────────────────────────────────────────────────────
#
# Bit layout (8-bit byte, lower 2 bits unused/zero):
#   bits [7:6] = dst   (2-bit, valid 0..3 = VA/VB/VC/VM)
#   bits [5:4] = src1  (2-bit, valid 0..3)
#   bits [3:2] = src2  (2-bit, valid 0..3)
#   bits [1:0] = 0     (reserved, always zero)
#
# Note: VL (code 4) is a 5th VU pointer register but does NOT fit in 2 bits.
#       It cannot appear in the dst/src1/src2 fields of the regs byte.
#
# encode(dst, src1, src2): (dst << 6) | (src1 << 4) | (src2 << 2)
# decode(byte):            dst = byte[7:6], src1 = byte[5:4], src2 = byte[3:2]
#
# Algebraic identity: encode(decode(b)) = b & 0xFC  (left-inverse)


def _z3_encode_vu_regs(
    dst: z3.BitVecRef, src1: z3.BitVecRef, src2: z3.BitVecRef
) -> z3.BitVecRef:
    return (dst << 6) | (src1 << 4) | (src2 << 2)


def _z3_decode_vu_regs(
    byte: z3.BitVecRef,
) -> tuple[z3.BitVecRef, z3.BitVecRef, z3.BitVecRef]:
    dst = z3.LShR(byte, 6) & 0x03
    src1 = z3.LShR(byte, 4) & 0x03
    src2 = z3.LShR(byte, 2) & 0x03
    return dst, src1, src2


def verify_vu_regs() -> None:
    print("VU_REGS encoding")
    dst = z3.BitVec("dst", 8)
    src1 = z3.BitVec("src1", 8)
    src2 = z3.BitVec("src2", 8)

    valid = z3.And(z3.ULE(dst, 3), z3.ULE(src1, 3), z3.ULE(src2, 3))

    enc = _z3_encode_vu_regs(dst, src1, src2)
    d_dst, d_src1, d_src2 = _z3_decode_vu_regs(enc)

    prove(d_dst == dst, valid, label="roundtrip: decoded dst == original dst")
    prove(d_src1 == src1, valid, label="roundtrip: decoded src1 == original src1")
    prove(d_src2 == src2, valid, label="roundtrip: decoded src2 == original src2")

    dst2 = z3.BitVec("dst2", 8)
    src1b = z3.BitVec("src1b", 8)
    src2b = z3.BitVec("src2b", 8)
    valid2 = z3.And(z3.ULE(dst2, 3), z3.ULE(src1b, 3), z3.ULE(src2b, 3))
    enc2 = _z3_encode_vu_regs(dst2, src1b, src2b)
    distinct = z3.Or(dst != dst2, src1 != src1b, src2 != src2b)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct,
        label="injectivity: distinct valid inputs → distinct bytes",
    )

    # Lower 2 bits are always zero
    prove((enc & 0x03) == 0, valid, label="lower 2 bits always zero (byte & 0x03 == 0)")

    # VL (code 4) does not fit: 4 > max 2-bit unsigned value
    vl_code = z3.BitVecVal(4, 8)
    prove(
        z3.UGT(vl_code, z3.BitVecVal(3, 8)),
        label="VL (code 4) cannot be encoded in a 2-bit field (4 > 3)",
    )

    # Left-inverse: encode(decode(b)) = b & 0xFC  for all b (universal)
    # Proof: ((b>>6)&3)<<6 | ((b>>4)&3)<<4 | ((b>>2)&3)<<2 = (b&0xC0)|(b&0x30)|(b&0x0C) = b&0xFC
    b = z3.BitVec("b_vu", 8)
    d_d, d_s1, d_s2 = _z3_decode_vu_regs(b)
    prove(
        _z3_encode_vu_regs(d_d, d_s1, d_s2) == (b & 0xFC),
        label="left-inverse: encode(decode(b)) == b & 0xFC (universal)",
    )
    print()


# ── ISA.json data checks ──────────────────────────────────────────────────────


def verify_isa_json(isa: dict[str, Any]) -> None:
    print("ISA.json data consistency")

    core = isa["instructions"]
    fp = isa["instructions_fp"]
    vu = isa["instructions_vu"]

    all_opcodes = [i["opcode"] for i in core + fp + vu]

    # D1 — opcode uniqueness
    check(
        len(set(all_opcodes)) == len(all_opcodes),
        f"D1: all {len(all_opcodes)} opcodes are unique",
    )

    # D2 — opcode ranges
    core_ops = [i["opcode"] for i in core]
    fp_ops = [i["opcode"] for i in fp]
    vu_ops = [i["opcode"] for i in vu]
    check(
        max(core_ops) <= 127 and min(core_ops) == 0,
        f"D2: core opcodes in 0-127 (got {min(core_ops)}-{max(core_ops)})",
    )
    check(
        min(fp_ops) == 128 and max(fp_ops) <= 162,
        f"D2: FP opcodes in 128-162 (got {min(fp_ops)}-{max(fp_ops)})",
    )
    check(
        min(vu_ops) == 163 and max(vu_ops) <= 183,
        f"D2: VU opcodes in 163-183 (got {min(vu_ops)}-{max(vu_ops)})",
    )
    check(min(fp_ops) > max(core_ops), "D2: no overlap between core and FP ranges")
    check(min(vu_ops) > max(fp_ops), "D2: no overlap between FP and VU ranges")

    # D3 — VU format codes
    vu_fmt_codes = [f["code"] for f in isa["vu_formats"]]
    check(vu_fmt_codes == list(range(7)), "D3: VU format codes are 0-6 in order")

    # D4 — VU mode codes
    vu_mode_codes = [m["code"] for m in isa["vu_modes"]]
    check(vu_mode_codes == list(range(4)), "D4: VU mode codes are 0-3 in order")

    # D5 — VU condition codes
    vu_cond_codes = [c["code"] for c in isa["vu_conditions"]]
    check(vu_cond_codes == list(range(6)), "D5: VU condition codes are 0-5 in order")

    # D6 — FP register FPM bytes are distinct
    reg_bytes = [_fpm_byte(r) for r in isa["fp_registers"]]
    check(
        len(set(reg_bytes)) == len(reg_bytes),
        f"D6: {len(isa['fp_registers'])} named FP registers have distinct FPM bytes",
    )

    # D7 — FP register (pos, fmt) validity per FP_FMT_MAX_POS
    invalid_regs = [
        r["name"]
        for r in isa["fp_registers"]
        if r["fmt"] in _FP_FMT_MAX_POS and r["pos"] > _FP_FMT_MAX_POS[r["fmt"]]
    ]
    check(
        len(invalid_regs) == 0,
        f"D7: all FP register positions valid for their format (violations: {invalid_regs})",
    )

    # D8 — FP format widths match constants
    mismatches = [
        f"{f['suffix']}(code={f['code']}): isa.json={f['width']}, constants={_FP_FMT_WIDTH[f['code']]}"
        for f in isa["fp_formats"]
        if f["code"] in _FP_FMT_WIDTH and f["width"] != _FP_FMT_WIDTH[f["code"]]
    ]
    check(len(mismatches) == 0, f"D8: FP format widths match constants ({mismatches})")

    # D9 — VU elem_size matches constants
    mismatches = [
        f"{f['suffix']}(code={f['code']}): isa.json={f['elem_size']}, constants={_VU_FMT_ELEM_SIZE[f['code']]}"
        for f in isa["vu_formats"]
        if f["code"] in _VU_FMT_ELEM_SIZE
        and f["elem_size"] != _VU_FMT_ELEM_SIZE[f["code"]]
    ]
    check(
        len(mismatches) == 0, f"D9: VU elem_size values match constants ({mismatches})"
    )

    # D10 — instruction size in [1,4] (current max; spec reserves up to 7 for future VU)
    size_errors = [
        f"{i['op']}: size={_isize(i)}"
        for i in core + fp + vu
        if not (1 <= _isize(i) <= 4)
    ]
    check(len(size_errors) == 0, f"D10: all instruction sizes in [1,4] ({size_errors})")

    # D11 — exactly 7 sync VU instructions (VSET×4 + VFSTAT + VFCLR + VWAIT)
    sync_ops = {i["op"] for i in vu if i.get("sync", False)}
    check(
        len(sync_ops) == 7,
        f"D11: exactly 7 sync VU instructions; got {len(sync_ops)}: {sync_ops}",
    )

    # D12 — FP format metadata consistency
    fp_fmt_codes = [f["code"] for f in isa["fp_formats"]]
    check(fp_fmt_codes == list(range(7)), "D12: FP format codes are 0-6 in order")
    fp_fmt_max_pos_mismatches = [
        f"{f['suffix']}(code={f['code']}): isa.json={f['max_pos']}, constants={_FP_FMT_MAX_POS[f['code']]}"
        for f in isa["fp_formats"]
        if f["code"] in _FP_FMT_MAX_POS and f["max_pos"] != _FP_FMT_MAX_POS[f["code"]]
    ]
    check(
        len(fp_fmt_max_pos_mismatches) == 0,
        f"D12: FP format max_pos matches constants ({fp_fmt_max_pos_mismatches})",
    )

    # D13 — since field: core instructions introduced in v1, FP in v2, VU in v3
    bad_since_core = [i["op"] for i in core if i.get("since") != 1]
    bad_since_fp = [i["op"] for i in fp if i.get("since") != 2]
    bad_since_vu = [i["op"] for i in vu if i.get("since") != 3]
    check(
        len(bad_since_core) == 0,
        f"D13: all core instructions have since=1 (violations: {bad_since_core})",
    )
    check(
        len(bad_since_fp) == 0,
        f"D13: all FP instructions have since=2 (violations: {bad_since_fp})",
    )
    check(
        len(bad_since_vu) == 0,
        f"D13: all VU instructions have since=3 (violations: {bad_since_vu})",
    )

    # D14 — all operand types from the known set (no typos, no undeclared types)
    unknown_ops: list[str] = []
    for i in core + fp + vu:
        for op in i["operands"]:
            if op not in _KNOWN_OPERAND_TYPES:
                unknown_ops.append(f"{i['op']}.{op}")
    check(
        len(unknown_ops) == 0,
        f"D14: all operand types from known set (unknown: {unknown_ops})",
    )

    # D15 — all instruction costs ≥ 0
    neg_costs = [
        f"{i['op']}(cost={i['cost']})" for i in core + fp + vu if i["cost"] < 0
    ]
    check(len(neg_costs) == 0, f"D15: all costs ≥ 0 ({neg_costs})")

    # D16 — VU operand structure
    bad_vcmp = [
        i["op"]
        for i in vu
        if i["op"] == "VCMP" and i["operands"] != ["imm", "imm", "imm"]
    ]
    check(
        len(bad_vcmp) == 0,
        f"D16: VCMP has exactly 3 imm operands (violations: {bad_vcmp})",
    )
    bad_async = [
        i["op"]
        for i in vu
        if not i.get("sync", False)
        and i["op"] != "VCMP"
        and i["operands"] != ["imm", "imm"]
    ]
    check(
        len(bad_async) == 0,
        f"D16: async non-VCMP VU ops have exactly 2 imm operands (violations: {bad_async})",
    )
    bad_sync = [
        f"{i['op']}: got {i['operands']}, expected {_VU_SYNC_OPERANDS[i['op']]}"
        for i in vu
        if i.get("sync", False) and i["operands"] != _VU_SYNC_OPERANDS.get(i["op"])
    ]
    check(
        len(bad_sync) == 0,
        f"D16: sync VU operand structure correct (violations: {bad_sync})",
    )

    # D17 — mnemonic aliases resolve to existing mnemonics
    all_mnemonics = {i["mnemonic"] for i in core + fp + vu}
    bad_aliases = [
        f"{alias}→{target}"
        for alias, target in isa["mnemonic_aliases"].items()
        if target not in all_mnemonics
    ]
    check(
        len(bad_aliases) == 0,
        f"D17: all alias targets are known mnemonics (broken: {bad_aliases})",
    )
    print()


# ── Main ──────────────────────────────────────────────────────────────────────


def main() -> int:
    global _quiet
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--quiet", action="store_true", help="Only print failures")
    args = parser.parse_args()
    _quiet = args.quiet

    isa = json.loads(_ISA_JSON.read_text())

    verify_regaddr()
    verify_fpm(isa)
    verify_vfm()
    verify_vu_regs()
    verify_isa_json(isa)

    n_fail = len(_failures)
    total = _passed + n_fail

    print(f"{'─' * 50}")
    print(f"  {_passed}/{total} passed", end="")
    if n_fail:
        print(f"  ← {n_fail} FAILED:")
        for f in _failures:
            print(f"    • {f}")
        return 1
    print("  ✓ all passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
