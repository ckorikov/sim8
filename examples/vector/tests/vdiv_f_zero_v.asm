; vdiv_f_zero_v.asm — Float16 edge: division by zero and 0/0
; Expected: dst = [inf, -inf, NaN, NaN, 0.5, -0.5, 2.0, -2.0]
; VFPSR: DZ + NV flags set

@page 1
src1:   DB 1.0_h, -1.0_h, 0.0_h, -0.0_h, 1.0_h, -1.0_h, 4.0_h, -8.0_h
src2:   DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 2.0_h, 2.0_h, 2.0_h, 4.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VDIV.H VC, VA, VB
    VWAIT
    VFSTAT A
    HLT
