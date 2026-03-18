; io.o2.asm
; API: print_o2
; In: FQA=value, A=fraction digits (0..3), D=cursor | Out: D=next
; Req: DP=0
;
; Example (DB -> print):
;   @include "std/io.o2.asm"
;   JMP start
; value: DB 1.5_o2
;
; start: FMOV.O2 FQA, [value]
;        MOV D, 232
;        CALL print_o2
;        HLT

o2_text_nan: DB "NaN"
             DB 0
o2_text_inf: DB "Inf"
             DB 0
o2_tmp_digits: DB 0

print_o2:
        CMP A, 3
        JBE o2_digits_ok
        MOV A, 3
o2_digits_ok:
        MOV [o2_tmp_digits], A

        FCLASS.O2 A, FQA
        MOV B, A

        AND A, 0x30
        JZ o2_not_nan
        MOV C, o2_text_nan
        JMP o2_print_string

o2_not_nan:
        MOV A, B
        AND A, 0x40
        JZ o2_not_negative
        MOV [D], 45
        INC D
        FNEG.O2 FQA

o2_not_negative:
        MOV A, B
        AND A, 0x08
        JZ o2_print_absolute
        MOV C, o2_text_inf
        JMP o2_print_string

o2_print_absolute:
        MOV C, [o2_tmp_digits]
        MOV A, 1
        FSCFG A
        FFTOI.O2 B, FQA
        FITOF.O2 FQB, B
        FSUB.O2 FQA, FQB
        MOV A, B
        PUSH C
        CALL o2_print_uint8_decimal
        POP C
        CMP C, 0
        JZ o2_done

        MOV [D], 46
        INC D

        FMOV.O2 FQC, 10.0
o2_frac_loop:
        FMUL.O2 FQA, FQC
        MOV A, 1
        FSCFG A
        FFTOI.O2 B, FQA
        FITOF.O2 FQB, B
        FSUB.O2 FQA, FQB
        MOV A, B
        ADD A, 48
        MOV [D], A
        INC D
        DEC C
        JNZ o2_frac_loop

o2_done:
        MOV B, 0
        FSCFG B
        RET

o2_print_string:
        MOV A, [C]
        CMP A, 0
        JZ o2_print_string_done
        MOV [D], A
        INC C
        INC D
        JMP o2_print_string
o2_print_string_done:
        RET

o2_print_uint8_decimal:
        MOV B, A
        MOV C, 0
o2_decimal_encode_loop:
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
        JNZ o2_decimal_encode_loop
o2_decimal_print_loop:
        POP A
        MOV [D], A
        INC D
        DEC C
        JNZ o2_decimal_print_loop
        RET
