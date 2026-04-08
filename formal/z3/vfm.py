"""VFM encoding verification.

Bit layout (8-bit byte, upper 3 bits unused/zero):
  bits [7:5] = 0    (reserved, always zero)
  bits [4:3] = mode (2-bit, valid 0..3)
  bits [2:0] = fmt  (3-bit, valid 0..6)

encode(fmt, mode): (mode << 3) | fmt
decode(byte):      fmt = byte & 0x07,  mode = (byte >> 3) & 0x03
  Note: cond is NOT stored in the VFM byte; it is a separate byte in VCMP.

Algebraic identity: encode(decode(b)) = b & 0x1F  (left-inverse)
"""

from __future__ import annotations

import z3

from harness import prove


def _z3_encode(fmt: z3.BitVecRef, mode: z3.BitVecRef) -> z3.BitVecRef:
    return (mode << 3) | fmt


def _z3_decode(byte: z3.BitVecRef) -> tuple[z3.BitVecRef, z3.BitVecRef]:
    """Returns (fmt, mode)."""
    fmt = byte & 0x07
    mode = z3.LShR(byte, 3) & 0x03
    return fmt, mode


def verify() -> None:
    print("VFM encoding")
    fmt = z3.BitVec("fmt", 8)
    mode = z3.BitVec("mode", 8)

    valid = z3.And(z3.ULE(fmt, 6), z3.ULE(mode, 3))

    enc = _z3_encode(fmt, mode)
    d_fmt, d_mode = _z3_decode(enc)

    prove(d_fmt == fmt, valid, label="roundtrip: decoded fmt == original fmt")
    prove(d_mode == mode, valid, label="roundtrip: decoded mode == original mode")

    fmt2 = z3.BitVec("fmt2", 8)
    mode2 = z3.BitVec("mode2", 8)
    valid2 = z3.And(z3.ULE(fmt2, 6), z3.ULE(mode2, 3))
    enc2 = _z3_encode(fmt2, mode2)
    distinct = z3.Or(fmt != fmt2, mode != mode2)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct,
        label="injectivity: distinct valid inputs → distinct bytes",
    )

    prove(z3.ULE(enc, 0x1F), valid, label="upper 3 bits always zero (byte ≤ 0x1F)")

    # Left-inverse: encode(decode(b)) = b & 0x1F  for all b
    byte = z3.BitVec("byte_vfm", 8)
    d_f, d_m = _z3_decode(byte)
    prove(
        _z3_encode(d_f, d_m) == (byte & 0x1F),
        label="left-inverse: encode(decode(b)) == b & 0x1F (universal)",
    )
    print()
