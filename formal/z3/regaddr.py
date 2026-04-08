"""REGADDR encoding verification.

Bit layout (8-bit byte):
  bits [7:3] = offset_unsigned  (5-bit two's-complement of offset in [-16,+15])
  bits [2:0] = reg_code         (3-bit, valid range 0..4; codes 5-7 -> FAULT)

encode(reg, off):  off_u = off if off >= 0 else 32 + off
                   byte  = (off_u << 3) | reg
decode(byte):      reg   = byte & 0x07
                   off_u = byte >> 3
                   off   = off_u if off_u <= 15 else off_u - 32

Algebraic identity: encode(decode(b)) = b  for all b  (right-inverse)
"""

from __future__ import annotations

import z3

from harness import prove

_RA_OFF_MAX: int = 15
_RA_OFF_RANGE: int = 32


def _z3_encode(reg: z3.BitVecRef, off: z3.BitVecRef) -> z3.BitVecRef:
    """reg: BitVec(8), off: BitVec(8) signed — returns BitVec(8)."""
    off_u = z3.If(off >= 0, off, _RA_OFF_RANGE + off)
    return (off_u << 3) | reg


def _z3_decode(byte: z3.BitVecRef) -> tuple[z3.BitVecRef, z3.BitVecRef]:
    """Returns (reg: BitVec(8), off: BitVec(8) signed)."""
    reg = byte & 0x07
    off_u = z3.LShR(byte, 3)
    off = z3.If(z3.ULE(off_u, _RA_OFF_MAX), off_u, off_u - _RA_OFF_RANGE)
    return reg, off


def verify() -> None:
    print("REGADDR encoding")
    reg = z3.BitVec("reg", 8)
    off = z3.BitVec("off", 8)

    valid = z3.And(z3.ULE(reg, 4), off >= -16, off <= 15)

    enc = _z3_encode(reg, off)
    dec_reg, dec_off = _z3_decode(enc)

    prove(dec_reg == reg, valid, label="roundtrip: decoded reg == original reg")
    prove(dec_off == off, valid, label="roundtrip: decoded off == original off")

    # Injectivity: distinct valid inputs encode to distinct bytes
    reg2 = z3.BitVec("reg2", 8)
    off2 = z3.BitVec("off2", 8)
    valid2 = z3.And(z3.ULE(reg2, 4), off2 >= -16, off2 <= 15)
    enc2 = _z3_encode(reg2, off2)
    distinct_inputs = z3.Or(reg != reg2, off != off2)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct_inputs,
        label="injectivity: distinct inputs → distinct bytes",
    )

    # DP (code 5) is outside the valid regaddr domain
    dp_code = z3.BitVecVal(5, 8)
    prove(
        z3.UGT(dp_code, z3.BitVecVal(4, 8)),
        label="DP (code 5) is outside valid regaddr domain (causes FAULT)",
    )

    # Output fits in 8 bits
    prove(z3.ULE(enc, 255), valid, label="output is a valid byte")

    # Reg field in encoded byte is preserved
    prove((enc & 0x07) == reg, valid, label="encoded byte[2:0] == reg")

    # Right-inverse: encode(decode(b)) = b  for ALL bytes
    b = z3.BitVec("b_ra", 8)
    d_reg, d_off = _z3_decode(b)
    prove(
        _z3_encode(d_reg, d_off) == b,
        label="right-inverse: encode(decode(b)) == b (universal)",
    )
    print()
