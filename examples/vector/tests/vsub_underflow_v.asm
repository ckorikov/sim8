; vsub_underflow_v.asm — UINT8 underflow: 0-1=255 (mod 256)
; Expected: dst = [255, 0, 156, 1]

@page 1
src1:   DB 0, 1, 100, 255
src2:   DB 1, 1, 200, 254
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src1
    VSET VB, src2
    VSET VC, dst
    VSUB.U VC, VA, VB
    VWAIT
    HLT
