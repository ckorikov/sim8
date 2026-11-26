; vsub_f_v.asm — Vector float16: dst[i] = src1[i] - src2[i], 8 elements
; Expected: [9.0, 8.0, 7.0, 6.0, 5.0, 4.0, 3.0, 2.0]

@page 1
src1:   DB 10.0_h, 10.0_h, 10.0_h, 10.0_h, 10.0_h, 10.0_h, 10.0_h, 10.0_h
src2:   DB 1.0_h, 2.0_h, 3.0_h, 4.0_h, 5.0_h, 6.0_h, 7.0_h, 8.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VSUB.H VC, VA, VB
    VWAIT
    HLT
