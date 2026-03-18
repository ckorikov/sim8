; io_fp8e5_print — OFP8 E5M2 (FQA) as "-NNN.DD"
; In:  FQA = OFP8 E5M2, D = output cursor
; Out: D = next output position
; Trashes: A, B, C, FQA, FQB, FQC, FPCR (restored to RNE on exit)
; Req: DP = 0, @include "io.common.asm" before this file

io_fp8e5_print:
        FCLASS.O2 A, FQA
        MOV B, A

        AND A, 0x30
        JZ fe5_ci
        MOV C, io_s_nan
        JMP io_puts

fe5_ci:
        MOV A, B
        AND A, 0x08
        JZ fe5_cs
        MOV A, B
        AND A, 0x40
        JZ fe5_pi
        MOV [D], 45
        INC D
fe5_pi:
        MOV C, io_s_inf
        JMP io_puts

fe5_cs:
        MOV A, B
        AND A, 0x40
        JZ fe5_abs
        MOV [D], 45
        INC D
        FNEG.O2 FQA

fe5_abs:
        MOV A, 1
        FSCFG A
        FFTOI.O2 B, FQA
        FITOF.O2 FQB, B
        FSUB.O2 FQA, FQB
        MOV A, B
        CALL io_itoa
        FMOV.O2 FQC, 10.0
        FMUL.O2 FQA, FQC
        FFTOI.O2 C, FQA
        FITOF.O2 FQB, C
        FSUB.O2 FQA, FQB
        FMUL.O2 FQA, FQC
        FFTOI.O2 A, FQA
        MOV B, 0
        FSCFG B
        JMP io_dot2d
