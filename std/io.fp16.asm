; io_fp16_print — float16 (FHA) as "-NNN.DD"
; In:  FHA = float16, D = output cursor
; Out: D = next output position
; Trashes: A, B, C, FHA, FHB, FHD, FPCR (restored to RNE on exit)
; Req: DP = 0, @include "io.common.asm" before this file

io_fp16_print:
        FCLASS.H A, FHA
        MOV B, A

        AND A, 0x30
        JZ fp16_ci
        MOV C, io_s_nan
        JMP io_puts

fp16_ci:
        MOV A, B
        AND A, 0x08
        JZ fp16_cs
        MOV A, B
        AND A, 0x40
        JZ fp16_pi
        MOV [D], 45
        INC D
fp16_pi:
        MOV C, io_s_inf
        JMP io_puts

fp16_cs:
        MOV A, B
        AND A, 0x40
        JZ fp16_abs
        MOV [D], 45
        INC D
        FNEG.H FHA

fp16_abs:
        MOV A, 1
        FSCFG A
        FFTOI.H B, FHA
        FITOF.H FHB, B
        FSUB.H FHA, FHB
        MOV A, B
        CALL io_itoa
        FMOV.H FHD, 10.0
        FMUL.H FHA, FHD
        FFTOI.H C, FHA
        FITOF.H FHB, C
        FSUB.H FHA, FHB
        FMUL.H FHA, FHD
        FFTOI.H A, FHA
        MOV B, 0
        FSCFG B
        JMP io_dot2d
