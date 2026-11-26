; vdiv_f_v.asm — Vector float16: dst[i] = src1[i] / src2[i], 8 elements
; Expected: [5.0, 5.0, 5.0, 5.0, 5.0, 5.0, 5.0, 5.0]

@page 1
src1:   DB 10.0_h, 20.0_h, 30.0_h, 40.0_h, 50.0_h, 60.0_h, 70.0_h, 80.0_h
src2:   DB 2.0_h, 4.0_h, 6.0_h, 8.0_h, 10.0_h, 12.0_h, 14.0_h, 16.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VDIV.H VC, VA, VB
    VWAIT
    HLT
