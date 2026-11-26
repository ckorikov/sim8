; vdiv_zero_v.asm — UINT8 division by zero → FAULT (ERR_DIV_ZERO=1)
; Expected: CPU state = FAULT after VWAIT

@page 1
src1:   DB 10, 20
src2:   DB 5, 0           ; second element is div-by-zero
dst:    DB 0, 0

@page 0
    VSET VL, 2
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VDIV.U VC, VA, VB
    VWAIT
    HLT
