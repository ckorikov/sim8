; vsqrt_f_neg_v.asm — Float16 edge: sqrt of negative/special values
; Expected: dst = [NaN, 0.0, 1.0, 2.0, inf, NaN, 3.0, 4.0]
; VFPSR: NV flag set for sqrt(-1) and sqrt(NaN)

@page 1
src:    DB -1.0_h, 0.0_h, 1.0_h, 4.0_h, inf_h, nan_h, 9.0_h, 16.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src
    VSET VB, dst
    VSQRT.H VB, VA
    VWAIT
    VFSTAT A
    HLT
