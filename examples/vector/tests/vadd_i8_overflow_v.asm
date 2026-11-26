; vadd_i8_overflow_v.asm — INT8 signed overflow: 127+1 → -128 (wrapping)
; Input: [127, -128, 100, -1] + [1, -1, 100, -1]
; Expected (wrapping): [-128, 127, -56, -2] → [0x80, 0x7F, 0xC8, 0xFE]

@page 1
src1:   DB 0x7F, 0x80, 0x64, 0xFF    ; 127, -128, 100, -1
src2:   DB 0x01, 0xFF, 0x64, 0xFF    ; 1, -1, 100, -1
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VADD.I VC, VA, VB
    VWAIT
    HLT
