; vsub_v.asm — Vector: dst[i] = src1[i] - src2[i], 4 elements
; Expected output at 0x010C: 9, 18, 27, 36

@page 1
src1:   DB 10, 20, 30, 40
src2:   DB 1, 2, 3, 4
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst

    VSUB.U VC, VA, VB
    VWAIT
    HLT
