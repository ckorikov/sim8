; io.fp32.asm
; API: print_fp32
; In: FA=value, A=fraction digits (0..6), D=cursor
; Out: D=next
; Req: DP=0
;
; Example (DB -> print):
;   @include "std/io.fp32.asm"
;   JMP start
; value: DB 1.3_f
;
; start: FMOV.F FA, [value]
;        MOV A, 1
;        MOV D, 232
;        CALL print_fp32
;        HLT

fp32_constant_half_float32: DB 0x00, 0x00, 0x00, 0x3F
fp32_constant_ten_float32: DB 0x00, 0x00, 0x20, 0x41

fp32_print_uint8_decimal:
        MOV B, A
        MOV C, 0
fp32_decimal_encode_loop:
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
        JNZ fp32_decimal_encode_loop
fp32_decimal_print_loop:
        POP A
        MOV [D], A
        INC D
        DEC C
        JNZ fp32_decimal_print_loop
        RET

print_fp32:
        ; Compact FPU path: integer part + per-digit fractional extraction.
        PUSH A
        FCLASS.F A, FA
        AND A, 0x40
        JZ fp32_abs
        MOV [D], 45
        INC D
        FNEG.F FA

fp32_abs:
        POP A
        CMP A, 6
        JBE fp32_digits_ok
        MOV A, 6
fp32_digits_ok:
        MOV C, A

        ; Integer part (truncate toward zero)
        MOV A, 1
        FSCFG A
        FFTOI.F A, FA
        PUSH A
        FITOF.F FB, A
        FSUB.F FA, FB
        POP A
        PUSH C
        CALL fp32_print_uint8_decimal
        POP C

        CMP C, 0
        JZ fp32_done

        MOV [D], 46
        INC D

fp32_frac_loop:
        FMOV.F FB, [fp32_constant_ten_float32]
        FMUL.F FA, FB
        MOV A, 1
        FSCFG A
        FFTOI.F B, FA
        FITOF.F FB, B
        FSUB.F FA, FB

        MOV A, B
        ADD A, 48
        MOV [D], A
        INC D

        DEC C
        JNZ fp32_frac_loop

fp32_done:
        MOV B, 0
        FSCFG B
        RET
