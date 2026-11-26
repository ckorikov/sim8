; vneg_v.asm — Vector: dst[i] = -src[i] (two's complement), 4 elements
; Expected output at 0x0108: 0xF6(-10), 0xEC(-20), 0xE2(-30), 0xD8(-40)

@page 1
src:    DB 10, 20, 30, 40
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src
    VSET VB, dst

    VNEG.U VB, VA
    VWAIT
    HLT
