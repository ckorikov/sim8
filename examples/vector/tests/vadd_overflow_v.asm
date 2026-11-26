; vadd_overflow_v.asm — UINT8 overflow: 200+100=300 → 44 (mod 256)
; Expected: dst = [44, 2, 0, 255]

@page 1
src1:   DB 200, 255, 128, 127
src2:   DB 100, 3, 128, 128
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VADD.U VC, VA, VB
    VWAIT
    HLT
