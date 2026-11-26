; vadd_reduce_v.asm — Vector reduction: dst = sum(src), 4 elements
; Expected output at 0x0108: 100 (10+20+30+40)

@page 1
src:    DB 10, 20, 30, 40
dst:    DB 0

@page 0
    VSET VL, 4
    VSET VA, src
    VSET VC, dst

    VADD.U VC, VA
    VWAIT
    HLT
