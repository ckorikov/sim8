; vadd_s.asm — Scalar: A[i] = B[i] + C[i], 4 elements
; Expected output at 0x010C: 11, 22, 33, 44

@page 1
src1:   DB 10, 20, 30, 40
src2:   DB 1, 2, 3, 4
dst:    DB 0, 0, 0, 0

@page 0
    MOV C, src1
    MOV D, 1           ; DP = page 1

    MOV A, [C]          ; A = src1[0]
    ADD A, 4            ; + src2[0] (offset 4) — load manually
    ; Actually do element-by-element with loop:

    MOV C, 0            ; i = 0
.loop:
    MOV A, [C]          ; A = src1[i]
    PUSH C
    ADD C, 4
    MOV B, [C]          ; B = src2[i]
    POP C
    ADD A, B            ; A = src1[i] + src2[i]
    PUSH C
    ADD C, 8
    MOV [C], A          ; dst[i] = A
    POP C
    INC C
    CMP C, 4
    JNZ .loop

    HLT
