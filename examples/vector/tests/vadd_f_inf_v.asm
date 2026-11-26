; vadd_f_inf_v.asm — Float16 edge: inf arithmetic
; Expected: dst = [inf, NaN, inf, -inf, NaN, inf, 0.0, NaN]
; VFPSR: NV flag set (inf + (-inf) = NaN)

@page 1
src1:   DB inf_h, inf_h, -inf_h, -inf_h, inf_h, 1.0_h, inf_h, nan_h
src2:   DB 1.0_h, -inf_h, -1.0_h, inf_h, inf_h, inf_h, -inf_h, 1.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VADD.H VC, VA, VB
    VWAIT
    VFSTAT A
    HLT
