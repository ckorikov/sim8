; io.fp16.asm
; API: print_fp16
; In: FHA=value, A=fraction digits (0..6), D=cursor | Out: D=next
; Req: DP=0
;
; Example (DB -> print):
;   @include "std/io.fp16.asm"
;   JMP start
; value: DB 1.5_h
;
; start: FMOV.H FHA, [value]
;        MOV D, 232
;        CALL print_fp16
;        HLT

fp16_text_nan: DB "NaN"
               DB 0
fp16_text_inf: DB "Inf"
               DB 0
fp16_tmp_digits: DB 0

print_fp16:
        CMP A, 6
        JBE fp16_digits_ok
        MOV A, 6
fp16_digits_ok:
        MOV [fp16_tmp_digits], A

        FCLASS.H A, FHA
        MOV B, A

        AND A, 0x30
        JZ fp16_not_nan
        MOV C, fp16_text_nan
        JMP fp16_print_string

fp16_not_nan:
        MOV A, B
        AND A, 0x40
        JZ fp16_not_negative
        MOV [D], 45
        INC D
        FNEG.H FHA

fp16_not_negative:
        MOV A, B
        AND A, 0x08
        JZ fp16_print_absolute
        MOV C, fp16_text_inf
        JMP fp16_print_string

fp16_print_absolute:
        MOV C, [fp16_tmp_digits]
        MOV A, 1
        FSCFG A
        FFTOI.H B, FHA
        FITOF.H FHB, B
        FSUB.H FHA, FHB
        MOV A, B
        PUSH C
        CALL fp16_print_uint8_decimal
        POP C
        CMP C, 0
        JZ fp16_done

        MOV [D], 46
        INC D

        FMOV.H FHD, 10.0
fp16_frac_loop:
        FMUL.H FHA, FHD
        MOV A, 1
        FSCFG A
        FFTOI.H B, FHA
        FITOF.H FHB, B
        FSUB.H FHA, FHB
        MOV A, B
        ADD A, 48
        MOV [D], A
        INC D
        DEC C
        JNZ fp16_frac_loop

fp16_done:
        MOV B, 0
        FSCFG B
        RET

fp16_print_string:
        MOV A, [C]
        CMP A, 0
        JZ fp16_print_string_done
        MOV [D], A
        INC C
        INC D
        JMP fp16_print_string
fp16_print_string_done:
        RET

fp16_print_uint8_decimal:
        MOV B, A
        MOV C, 0
fp16_decimal_encode_loop:
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
        JNZ fp16_decimal_encode_loop
fp16_decimal_print_loop:
        POP A
        MOV [D], A
        INC D
        DEC C
        JNZ fp16_decimal_print_loop
        RET
