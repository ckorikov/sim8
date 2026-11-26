; vmov_v.asm — Vector: copy 4 bytes from src to dst
; Expected output at 0x0108: 0xAA, 0xBB, 0xCC, 0xDD

@page 1
src:    DB 0xAA, 0xBB, 0xCC, 0xDD
dst:    DB 0, 0, 0, 0

@page 0
    VSET VL, 4
    VSET VA, src
    VSET VB, dst

    VMOV.U VB, VA
    VWAIT
    HLT
