; vl_zero_v.asm — VL=0: all ops are no-ops, memory unchanged
; Expected: dst stays 0xDE, 0xAD

@page 1
src:    DB 0xFF, 0xFF
dst:    DB 0xDE, 0xAD

@page 0
    VSET VL, 0
    VSET VA, src
    VSET VB, dst
    VADD.U VB, VA, VA
    VMUL.U VB, VA, VA
    VMOV.U VB, VA
    VWAIT
    HLT
