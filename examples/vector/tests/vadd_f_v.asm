; vadd_f_v.asm — Vector float16: dst[i] = src1[i] + src2[i], 8 elements
; Expected: [1.5, 3.5, 5.5, 7.5, 9.5, 11.5, 13.5, 15.5]

@page 1
src1:   DB 1.0_h, 2.0_h, 3.0_h, 4.0_h, 5.0_h, 6.0_h, 7.0_h, 8.0_h
src2:   DB 0.5_h, 1.5_h, 2.5_h, 3.5_h, 4.5_h, 5.5_h, 6.5_h, 7.5_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VADD.H VC, VA, VB
    VWAIT
    HLT
