; vmax_v.asm — Vector: dst[i] = max(src1[i], src2[i]), 4 elements
; Expected output at 0x010C: 10, 20, 30, 40

@page 1
src1:   DB 10, 5, 30, 15
src2:   DB 3, 20, 7, 40
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst

    VMAX.U VC, VA, VB
    VWAIT
    HLT
