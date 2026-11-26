; vmul_f_v.asm — Vector float16: dst[i] = src1[i] * src2[i], 8 elements
; Expected: [2.0, 6.0, 12.0, 20.0, 30.0, 42.0, 56.0, 72.0]

@page 1
src1:   DB 1.0_h, 2.0_h, 3.0_h, 4.0_h, 5.0_h, 6.0_h, 7.0_h, 8.0_h
src2:   DB 2.0_h, 3.0_h, 4.0_h, 5.0_h, 6.0_h, 7.0_h, 8.0_h, 9.0_h
dst:    DB 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h, 0.0_h

@page 0
    VSET VL, 8
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VMUL.H VC, VA, VB
    VWAIT
    HLT
