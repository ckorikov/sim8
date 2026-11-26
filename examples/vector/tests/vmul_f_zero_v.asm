; vmul_f_zero_v.asm — Float16 edge: 0*inf=NaN, sign propagation
; Expected: dst = [NaN, NaN, 0.0, -0.0, 1.0, -1.0, 0.0, 0.0]
; VFPSR: NV flag set

@page 1
src1:   DB 0.0_h, -0.0_h, 0.0_h, -0.0_h, 1.0_h, -1.0_h, 0.0_h, 0.0_h
src2:   DB inf_h, inf_h, 1.0_h, 1.0_h, 1.0_h, 1.0_h, 0.0_h, -0.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VMUL.H VC, VA, VB
    VWAIT
    VFSTAT A
    HLT
