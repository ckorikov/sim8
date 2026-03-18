; io_fp8e4_print — OFP8 E4M3 (FQA) as "-NNN.DD"
; E4M3 has NO Infinity; max finite = ±448 (FFTOI saturates to 255)
; In:  FQA = OFP8 E4M3, D = output cursor
; Out: D = next output position
; Trashes: A, B, C, FQA, FQB, FQC, FPCR (restored to RNE on exit)
; Req: DP = 0, @include "io.common.asm" before this file

io_fp8e4_print:
        FCLASS.O3 A, FQA
        MOV B, A

        AND A, 0x30
        JZ fe4_cs
        MOV C, io_s_nan
        JMP io_puts

fe4_cs:
        MOV A, B
        AND A, 0x40
        JZ fe4_abs
        MOV [D], 45
        INC D
        FNEG.O3 FQA

fe4_abs:
        MOV A, 1
        FSCFG A
        FFTOI.O3 B, FQA
        FITOF.O3 FQB, B
        FSUB.O3 FQA, FQB
        MOV A, B
        CALL io_itoa
        FMOV.O3 FQC, 10.0
        FMUL.O3 FQA, FQC
        FFTOI.O3 C, FQA
        FITOF.O3 FQB, C
        FSUB.O3 FQA, FQB
        FMUL.O3 FQA, FQC
        FFTOI.O3 A, FQA
        MOV B, 0
        FSCFG B
        JMP io_dot2d
