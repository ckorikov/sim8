; vmov_s.asm — Scalar: copy 4 bytes from src to dst
; Expected output at 0x0108: 0xAA, 0xBB, 0xCC, 0xDD

@page 1
src:    DB 0xAA, 0xBB, 0xCC, 0xDD
dst:    DB 0, 0, 0, 0

@page 0
    MOV D, 1
    MOV C, 0
.loop:
    MOV A, [C]
    PUSH C
    ADD C, 4
    MOV [C], A
    POP C
    INC C
    CMP C, 4
    JNZ .loop
    HLT
