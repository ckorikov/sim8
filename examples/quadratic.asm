; Quadratic equation solver: ax^2 + bx + c = 0
; x = (-b +/- sqrt(b^2 - 4ac)) / (2a)

        JMP start

output: DB 232
coef_a: DB 1.0_h                 ; a = 1
coef_b: DB -5.0_h                ; b = -5
coef_c: DB 6.0_h                 ; c = 6

msg_x1:     DB "x1="
            DB 0
msg_x2:     DB " x2="
            DB 0
msg_err:    DB "no real"
            DB 0

start:
        ; 2a -> FHC
        FMOV.H FHC, 2.0
        FMUL.H FHC, [coef_a]    ; FHC = 2a

        ; discriminant D -> FHA
        CALL calc_discriminant

        ; Check D < 0
        FMOV.H FHB, 0.0
        FCMP.H FHA, FHB
        JC no_real

        FSQRT.H FHA
        FMOV.H FHD, FHA          ; FHD = sqrt(D), survives print_f16_3

        ; x1 -> FHA
        CALL calc_x1

        MOV D, [output]         ; Point to output
        MOV C, msg_x1
        CALL print
        CALL print_f16_3

        ; x2 -> FHA
        CALL calc_x2

        MOV C, msg_x2
        CALL print
        CALL print_f16_3

        JMP finish

no_real:
        MOV C, msg_err
        MOV D, [output]
        CALL print

finish:
        FSTAT A                  ; Read FP status
        HLT                      ; Stop execution

; --- Subroutines ---

; D = b^2 - 4ac
; Out: FHA = D
; Modifies: FHA, FHB
calc_discriminant:
        FMOV.H FHA, [coef_b]
        FMUL.H FHA, FHA         ; FHA = b^2
        FMOV.H FHB, 4.0
        FMUL.H FHB, [coef_a]
        FMUL.H FHB, [coef_c]    ; FHB = 4ac
        FSUB.H FHA, FHB         ; FHA = D
        RET

; x1 = (-b + sqrt(D)) / (2a)
; In:  FHD = sqrt(D), FHC = 2a
; Out: FHA = x1
; Modifies: FHA
calc_x1:
        FMOV.H FHA, [coef_b]
        FNEG.H FHA               ; FHA = -b
        FADD.H FHA, FHD          ; FHA = -b + sqrt(D)
        FDIV.H FHA, FHC          ; FHA = x1
        RET

; x2 = (-b - sqrt(D)) / (2a)
; In:  FHD = sqrt(D), FHC = 2a
; Out: FHA = x2
; Modifies: FHA
calc_x2:
        FMOV.H FHA, [coef_b]
        FNEG.H FHA               ; FHA = -b
        FSUB.H FHA, FHD          ; FHA = -b - sqrt(D)
        FDIV.H FHA, FHC          ; FHA = x2
        RET

put_char:                        ; put_char(A:char, D:*to)
        MOV [D], A               ; Write char to output
        INC D
        RET

print:                           ; print(C:*from, D:*to)
.loop:  MOV A, [C]
        CMP A, 0                 ; Check if end
        JZ .done
        CALL put_char
        INC C
        JMP .loop
.done:  RET

; Print FHA as decimal with 3 fractional digits
; Modifies: FHA, FHB, A, C
print_f16_3:
        MOV A, 1                 ; Truncate mode
        FSCFG A

        FMOV.H FHB, 0.0
        FCMP.H FHA, FHB
        JNC .non_negative
        MOV A, '-'                ; Print sign
        CALL put_char
        FNEG.H FHA

.non_negative:
        FFTOI.H A, FHA            ; Integer part
        FITOF.H FHB, A
        FSUB.H FHA, FHB           ; FHA = fractional part
        ADD A, '0'
        CALL put_char

        MOV A, '.'
        CALL put_char

        MOV C, 3                  ; 3 decimal digits
.frac_loop:
        FMOV.H FHB, 10.0
        FMUL.H FHA, FHB           ; Shift left one digit
        FFTOI.H A, FHA
        FITOF.H FHB, A
        FSUB.H FHA, FHB           ; Remove integer part
        ADD A, '0'
        CALL put_char
        DEC C
        JNZ .frac_loop
        RET
