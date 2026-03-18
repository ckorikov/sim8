; io.int.asm
; API: print_int
; In: A=uint8, D=cursor (232..255) | Out: D=next
;
; Example (DB -> print):
;   @include "std/io.int.asm"
;   JMP start
; value: DB 42
;
; start: MOV A, [value]
;        MOV D, 232
;        CALL print_int
;        HLT

print_int:
        PUSH A
        PUSH B
        PUSH C
        MOV B, A
        MOV C, 0
int_decimal_encode_loop:
        MOV A, B
        DIV 10
        PUSH A
        MUL 10
        SUB B, A
        ADD B, 48
        POP A
        PUSH B
        MOV B, A
        INC C
        CMP B, 0
        JNZ int_decimal_encode_loop
int_decimal_print_loop:
        POP A
        MOV [D], A
        INC D
        DEC C
        JNZ int_decimal_print_loop
        POP C
        POP B
        POP A
        RET
