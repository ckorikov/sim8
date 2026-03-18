; io_fp32_print — float32 (FA) as "-NNN.DD"
; In:  FA = float32, D = output cursor
; Out: D = next output position
; Trashes: A, B, C, FA, FB, FPCR (restored to RNE on exit)
; Req: DP = 0, @include "io.common.asm" before this file

fp32_c10: DB 0x00, 0x00, 0x20, 0x41

io_fp32_print:
        FCLASS.F A, FA
        MOV B, A

        AND A, 0x30
        JZ fp32_ci
        MOV C, io_s_nan
        JMP io_puts

fp32_ci:
        MOV A, B
        AND A, 0x08
        JZ fp32_cs
        MOV A, B
        AND A, 0x40
        JZ fp32_pi
        MOV [D], 45
        INC D
fp32_pi:
        MOV C, io_s_inf
        JMP io_puts

fp32_cs:
        MOV A, B
        AND A, 0x40
        JZ fp32_abs
        MOV [D], 45
        INC D
        FNEG.F FA

fp32_abs:
        MOV A, 1
        FSCFG A
        FFTOI.F B, FA
        FITOF.F FB, B
        FSUB.F FA, FB
        MOV A, B
        CALL io_itoa
        FMOV.F FB, [fp32_c10]
        FMUL.F FA, FB
        FFTOI.F C, FA
        FITOF.F FB, C
        FSUB.F FA, FB
        FMOV.F FB, [fp32_c10]
        FMUL.F FA, FB
        FFTOI.F A, FA
        MOV B, 0
        FSCFG B
        JMP io_dot2d
