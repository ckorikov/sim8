"""VU_REGS encoding verification.

Bit layout (8-bit byte, lower 2 bits unused/zero):
  bits [7:6] = dst   (2-bit, valid 0..3 = VA/VB/VC/VM)
  bits [5:4] = src1  (2-bit, valid 0..3)
  bits [3:2] = src2  (2-bit, valid 0..3)
  bits [1:0] = 0     (reserved, always zero)

Note: VL (code 4) is a 5th VU pointer register but does NOT fit in 2 bits.

encode(dst, src1, src2): (dst << 6) | (src1 << 4) | (src2 << 2)
decode(byte):            dst = byte[7:6], src1 = byte[5:4], src2 = byte[3:2]

Algebraic identity: encode(decode(b)) = b & 0xFC  (left-inverse)
"""

from __future__ import annotations

import z3

from harness import prove


def _z3_encode(dst: z3.BitVecRef, src1: z3.BitVecRef, src2: z3.BitVecRef) -> z3.BitVecRef:
    return (dst << 6) | (src1 << 4) | (src2 << 2)


def _z3_decode(
    byte: z3.BitVecRef,
) -> tuple[z3.BitVecRef, z3.BitVecRef, z3.BitVecRef]:
    dst = z3.LShR(byte, 6) & 0x03
    src1 = z3.LShR(byte, 4) & 0x03
    src2 = z3.LShR(byte, 2) & 0x03
    return dst, src1, src2


def verify() -> None:
    print("VU_REGS encoding")
    dst = z3.BitVec("dst", 8)
    src1 = z3.BitVec("src1", 8)
    src2 = z3.BitVec("src2", 8)

    valid = z3.And(z3.ULE(dst, 3), z3.ULE(src1, 3), z3.ULE(src2, 3))

    enc = _z3_encode(dst, src1, src2)
    d_dst, d_src1, d_src2 = _z3_decode(enc)

    prove(d_dst == dst, valid, label="roundtrip: decoded dst == original dst")
    prove(d_src1 == src1, valid, label="roundtrip: decoded src1 == original src1")
    prove(d_src2 == src2, valid, label="roundtrip: decoded src2 == original src2")

    dst2 = z3.BitVec("dst2", 8)
    src1b = z3.BitVec("src1b", 8)
    src2b = z3.BitVec("src2b", 8)
    valid2 = z3.And(z3.ULE(dst2, 3), z3.ULE(src1b, 3), z3.ULE(src2b, 3))
    enc2 = _z3_encode(dst2, src1b, src2b)
    distinct = z3.Or(dst != dst2, src1 != src1b, src2 != src2b)
    prove(
        enc != enc2,
        valid,
        valid2,
        distinct,
        label="injectivity: distinct valid inputs → distinct bytes",
    )

    prove((enc & 0x03) == 0, valid, label="lower 2 bits always zero (byte & 0x03 == 0)")

    # VL (code 4) does not fit in 2-bit field
    vl_code = z3.BitVecVal(4, 8)
    prove(
        z3.UGT(vl_code, z3.BitVecVal(3, 8)),
        label="VL (code 4) cannot be encoded in a 2-bit field (4 > 3)",
    )

    # Left-inverse: encode(decode(b)) = b & 0xFC  for all b
    b = z3.BitVec("b_vu", 8)
    d_d, d_s1, d_s2 = _z3_decode(b)
    prove(
        _z3_encode(d_d, d_s1, d_s2) == (b & 0xFC),
        label="left-inverse: encode(decode(b)) == b & 0xFC (universal)",
    )
    print()
