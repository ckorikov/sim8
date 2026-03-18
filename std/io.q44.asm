; io.q44.asm
; API: print_q44
; In: A=Q4.4 byte, D=cursor | Out: D=next
; Prints as I.H (example: 0x48 -> "4.8")
;
; Example (DB -> print):
;   @include "std/io.q44.asm"
;   JMP start
; value: DB 0x48
;
; start: MOV A, [value]
;        MOV D, 232
;        CALL print_q44
;        HLT

print_q44:
        PUSH A
        PUSH B
        MOV B, A

        SHR A, 4
        CMP A, 10
        JC q44_integer_single_digit
        PUSH A
        MOV A, 49
        MOV [D], A
        INC D
        POP A
        SUB A, 10
q44_integer_single_digit:
        ADD A, 48
        MOV [D], A
        INC D

        MOV A, 46
        MOV [D], A
        INC D

        MOV A, B
        AND A, 0x0F
        CMP A, 10
        JC q44_fraction_decimal_digit
        ADD A, 55
        JMP q44_fraction_write
q44_fraction_decimal_digit:
        ADD A, 48
q44_fraction_write:
        MOV [D], A
        INC D

        POP B
        POP A
        RET
