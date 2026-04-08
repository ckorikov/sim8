"""FPM encoding verification.

Bit layout (8-bit byte):
  bits [7:6] = phys  (2-bit, valid 0..1)
  bits [5:3] = pos   (3-bit, valid 0..FP_FMT_MAX_POS[fmt])
  bits [2:0] = fmt   (3-bit, valid 0..6; fmt 5-6 are N1/N2 reserved formats)

encode(phys, pos, fmt): (phys << 6) | (pos << 3) | fmt
decode(byte):           phys = byte[7:6] & 3,  pos = byte[5:3] & 7,  fmt = byte & 7

Algebraic identity: encode(decode(b)) = b  for all b  (right-inverse)
Structural bound:   valid byte <= 0x7E  (phys <= 1 -> bit 7 always 0)
"""

from __future__ import annotations

from typing import Any

import z3

from harness import check, prove


def _fpm_byte(r: dict[str, int]) -> int:
    return (r["phys"] << 6) | (r["pos"] << 3) | r["fmt"]


def _z3_encode(phys: z3.BitVecRef, pos: z3.BitVecRef, fmt: z3.BitVecRef) -> z3.BitVecRef:
    """All args BitVec(8) — returns BitVec(8)."""
    return (phys << 6) | (pos << 3) | fmt


def _z3_decode(
    byte: z3.BitVecRef,
) -> tuple[z3.BitVecRef, z3.BitVecRef, z3.BitVecRef]:
    """Returns (phys, pos, fmt) each BitVec(8)."""
    phys = z3.LShR(byte, 6) & 0x03
    pos = z3.LShR(byte, 3) & 0x07
    fmt = byte & 0x07
    return phys, pos, fmt


def _z3_max_pos(fmt: z3.BitVecRef) -> z3.BitVecRef:
    """FP_FMT_MAX_POS as a Z3 If-chain covering all 7 formats (0..6)."""
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


def verify(isa: dict[str, Any]) -> None:
    print("FPM encoding")
    phys = z3.BitVec("phys", 8)
    pos = z3.BitVec("pos", 8)
    fmt = z3.BitVec("fmt", 8)

    max_pos = _z3_max_pos(fmt)
    valid = z3.And(z3.ULE(phys, 1), z3.ULE(fmt, 6), z3.ULE(pos, max_pos))

    enc = _z3_encode(phys, pos, fmt)
    d_phys, d_pos, d_fmt = _z3_decode(enc)

    prove(d_phys == phys, valid, label="roundtrip: decoded phys == original phys")
    prove(d_pos == pos, valid, label="roundtrip: decoded pos == original pos")
    prove(d_fmt == fmt, valid, label="roundtrip: decoded fmt == original fmt")

    phys2 = z3.BitVec("phys2", 8)
    pos2 = z3.BitVec("pos2", 8)
    fmt2 = z3.BitVec("fmt2", 8)
    valid2 = z3.And(z3.ULE(phys2, 1), z3.ULE(fmt2, 6), z3.ULE(pos2, _z3_max_pos(fmt2)))
    enc2 = _z3_encode(phys2, pos2, fmt2)
    distinct = z3.Or(phys != phys2, pos != pos2, fmt != fmt2)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct,
        label="injectivity: distinct valid inputs → distinct bytes",
    )

    prove(
        z3.ULE(enc, 0x7E),
        valid,
        label="structural bound: valid FPM byte ≤ 0x7E (bit 7 always 0)",
    )

    # Right-inverse: encode(decode(b)) = b  for ALL bytes
    b = z3.BitVec("b_fpm", 8)
    d_p, d_pos_b, d_f = _z3_decode(b)
    prove(
        _z3_encode(d_p, d_pos_b, d_f) == b,
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
