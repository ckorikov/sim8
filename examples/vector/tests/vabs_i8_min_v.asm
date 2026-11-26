; vabs_i8_min_v.asm — INT8 edge: abs(-128) → -128 (wrapping, no positive repr)
; Expected: dst = [0x80, 0x01, 0x7F, 0x00]

@page 1
src:    DB 0x80, 0xFF, 0x81, 0x00    ; -128, -1, -127, 0
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src
    VSET VB, dst
    VABS.I VB, VA
    VWAIT
    HLT
