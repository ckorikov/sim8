; io.o3.asm
; API: print_o3
; In: FQA=value, A=fraction digits (0..3), D=cursor | Out: D=next
; E4M3 has no Infinity
; Req: DP=0
;
; Example (DB -> print):
;   @include "std/io.o3.asm"
;   JMP start
; value: DB 1.5_o3
;
; start: FMOV.O3 FQA, [value]
;        MOV D, 232
;        CALL print_o3
;        HLT

o3_text_nan: DB "NaN"
             DB 0
o3_tmp_digits: DB 0

print_o3:
        CMP A, 3
        JBE o3_digits_ok
        MOV A, 3
o3_digits_ok:
        MOV [o3_tmp_digits], A

        FCLASS.O3 A, FQA
        MOV B, A

        AND A, 0x30
        JZ o3_not_nan
        MOV C, o3_text_nan
        JMP o3_print_string

o3_not_nan:
        MOV A, B
        AND A, 0x40
        JZ o3_print_absolute
        MOV [D], 45
        INC D
        FNEG.O3 FQA

o3_print_absolute:
        MOV C, [o3_tmp_digits]
        MOV A, 1
        FSCFG A
        FFTOI.O3 B, FQA
        FITOF.O3 FQB, B
        FSUB.O3 FQA, FQB
        MOV A, B
        PUSH C
        CALL o3_print_uint8_decimal
        POP C
        CMP C, 0
        JZ o3_done

        MOV [D], 46
        INC D

        FMOV.O3 FQC, 10.0
o3_frac_loop:
        FMUL.O3 FQA, FQC
        MOV A, 1
        FSCFG A
        FFTOI.O3 B, FQA
        FITOF.O3 FQB, B
        FSUB.O3 FQA, FQB
        MOV A, B
        ADD A, 48
        MOV [D], A
        INC D
        DEC C
        JNZ o3_frac_loop

o3_done:
        MOV B, 0
        FSCFG B
        RET

o3_print_string:
        MOV A, [C]
        CMP A, 0
        JZ o3_print_string_done
        MOV [D], A
        INC C
        INC D
        JMP o3_print_string
o3_print_string_done:
        RET

o3_print_uint8_decimal:
        MOV B, A
        MOV C, 0
o3_decimal_encode_loop:
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
        JNZ o3_decimal_encode_loop
o3_decimal_print_loop:
        POP A
        MOV [D], A
        INC D
        DEC C
        JNZ o3_decimal_print_loop
        RET
