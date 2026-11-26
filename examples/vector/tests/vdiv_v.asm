; vdiv_v.asm — Vector: dst[i] = src1[i] / src2[i], 4 elements
; Expected output at 0x010C: 5, 10, 3, 2

@page 1
src1:   DB 20, 60, 30, 16
src2:   DB 4, 6, 10, 8
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst

    VDIV.U VC, VA, VB
    VWAIT
    HLT
