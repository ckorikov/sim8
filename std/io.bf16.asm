; io_bf16_print — bfloat16 (FHA) as "-NNN.DD"
; In:  FHA = bfloat16, D = output cursor
; Out: D = next output position
; Trashes: A, B, C, FHA, FHB, FHD, FPCR (restored to RNE on exit)
; Req: DP = 0, @include "io.common.asm" before this file

io_bf16_print:
        FCLASS.BF A, FHA
        MOV B, A

        AND A, 0x30
        JZ bf16_ci
        MOV C, io_s_nan
        JMP io_puts

bf16_ci:
        MOV A, B
        AND A, 0x08
        JZ bf16_cs
        MOV A, B
        AND A, 0x40
        JZ bf16_pi
        MOV [D], 45
        INC D
bf16_pi:
        MOV C, io_s_inf
        JMP io_puts

bf16_cs:
        MOV A, B
        AND A, 0x40
        JZ bf16_abs
        MOV [D], 45
        INC D
        FNEG.BF FHA

bf16_abs:
        MOV A, 1
        FSCFG A
        FFTOI.BF B, FHA
        FITOF.BF FHB, B
        FSUB.BF FHA, FHB
        MOV A, B
        CALL io_itoa
        FMOV.BF FHD, 10.0
        FMUL.BF FHA, FHD
        FFTOI.BF C, FHA
        FITOF.BF FHB, C
        FSUB.BF FHA, FHB
        FMUL.BF FHA, FHD
        FFTOI.BF A, FHA
        MOV B, 0
        FSCFG B
        JMP io_dot2d
