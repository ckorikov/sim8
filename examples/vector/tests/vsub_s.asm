; vsub_s.asm — Scalar: dst[i] = src1[i] - src2[i], 4 elements
; Expected output at 0x010C: 9, 18, 27, 36

@page 1
src1:   DB 10, 20, 30, 40
src2:   DB 1, 2, 3, 4
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
    SUB A, B
    PUSH C
    ADD C, 8
    MOV [C], A
    POP C
    INC C
    CMP C, 4
    JNZ .loop
    HLT
