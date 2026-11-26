; vabs_v.asm — Vector: dst[i] = abs(src[i]) as INT8, 4 elements
; Input INT8: -10, 20, -30, 40 → stored as 0xF6, 0x14, 0xE2, 0x28
; Expected output at 0x0108: 10, 20, 30, 40

@page 1
src:    DB 0xF6, 0x14, 0xE2, 0x28
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src
    VSET VB, dst

    VABS.I VB, VA
    VWAIT
    HLT
