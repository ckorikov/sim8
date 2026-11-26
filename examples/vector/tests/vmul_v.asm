; vmul_v.asm — Vector: dst[i] = src1[i] * src2[i], 4 elements
; Expected output at 0x010C: 20, 60, 30, 160

@page 1
src1:   DB 2, 3, 1, 4
src2:   DB 10, 20, 30, 40
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst

    VMUL.U VC, VA, VB
    VWAIT
    HLT
