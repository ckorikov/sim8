; io.bf16.asm
; API: print_bf16
; In: FHA=value, A=fraction digits (0..6), D=cursor | Out: D=next
; Req: DP=0
;
; Example (DB -> print):
;   @include "std/io.bf16.asm"
;   JMP start
; value: DB 2.5_bf
;
; start: FMOV.BF FHA, [value]
;        MOV D, 232
;        CALL print_bf16
;        HLT

bf16_text_nan: DB "NaN"
               DB 0
bf16_text_inf: DB "Inf"
               DB 0
bf16_tmp_digits: DB 0

print_bf16:
        CMP A, 6
        JBE bf16_digits_ok
        MOV A, 6
bf16_digits_ok:
        MOV [bf16_tmp_digits], A

        FCLASS.BF A, FHA
        MOV B, A

        AND A, 0x30
        JZ bf16_not_nan
        MOV C, bf16_text_nan
        JMP bf16_print_string

bf16_not_nan:
        MOV A, B
        AND A, 0x40
        JZ bf16_not_negative
        MOV [D], 45
        INC D
        FNEG.BF FHA

bf16_not_negative:
        MOV A, B
        AND A, 0x08
        JZ bf16_print_absolute
        MOV C, bf16_text_inf
        JMP bf16_print_string

bf16_print_absolute:
        MOV C, [bf16_tmp_digits]
        MOV A, 1
        FSCFG A
        FFTOI.BF B, FHA
        FITOF.BF FHB, B
        FSUB.BF FHA, FHB
        MOV A, B
        PUSH C
        CALL bf16_print_uint8_decimal
        POP C
        CMP C, 0
        JZ bf16_done

        MOV [D], 46
        INC D

        FMOV.BF FHD, 10.0
bf16_frac_loop:
        FMUL.BF FHA, FHD
        MOV A, 1
        FSCFG A
        FFTOI.BF B, FHA
        FITOF.BF FHB, B
        FSUB.BF FHA, FHB
        MOV A, B
        ADD A, 48
        MOV [D], A
        INC D
        DEC C
        JNZ bf16_frac_loop

bf16_done:
        MOV B, 0
        FSCFG B
        RET

bf16_print_string:
        MOV A, [C]
        CMP A, 0
        JZ bf16_print_string_done
        MOV [D], A
        INC C
        INC D
        JMP bf16_print_string
bf16_print_string_done:
        RET

bf16_print_uint8_decimal:
        MOV B, A
        MOV C, 0
bf16_decimal_encode_loop:
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
        JNZ bf16_decimal_encode_loop
bf16_decimal_print_loop:
        POP A
        MOV [D], A
        INC D
        DEC C
        JNZ bf16_decimal_print_loop
        RET
