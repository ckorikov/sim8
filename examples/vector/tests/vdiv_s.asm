; vdiv_s.asm — Scalar: dst[i] = src1[i] / src2[i], 4 elements
; Expected output at 0x010C: 5, 10, 3, 2

@page 1
src1:   DB 20, 60, 30, 16
src2:   DB 4, 6, 10, 8
dst:    DB 0, 0, 0, 0

@page 0
    MOV D, 1
    MOV C, 0
.loop:
    MOV A, [C]
    PUSH C
    ADD C, 4
    MOV B, [C]
    POP C
    DIV B
    PUSH C
    ADD C, 8
    MOV [C], A
    POP C
    INC C
    CMP C, 4
    JNZ .loop
    HLT
