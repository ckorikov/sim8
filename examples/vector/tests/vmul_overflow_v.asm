; vmul_overflow_v.asm — UINT8 overflow: 16*16=256 → 0 (mod 256)
; Expected: dst = [0, 64, 255, 4]
; 16*16=256→0, 200*200=40000→64, 255*1=255, 2*2=4

@page 1
src1:   DB 16, 200, 255, 2
src2:   DB 16, 200, 1, 2
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VMUL.U VC, VA, VB
    VWAIT
    HLT
