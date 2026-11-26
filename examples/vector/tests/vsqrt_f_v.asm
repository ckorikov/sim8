; vsqrt_f_v.asm — Vector float16: dst[i] = sqrt(src[i]), 8 elements
; Expected: [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0] (approx for non-perfect squares)

@page 1
src:    DB 1.0_h, 4.0_h, 9.0_h, 16.0_h, 25.0_h, 36.0_h, 49.0_h, 64.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src
    VSET VB, dst
    VSQRT.H VB, VA
    VWAIT
    HLT
