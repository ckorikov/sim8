; io_q44_print — Q4.4 fixed-point as "I.H"
; Format: bits [7:4] = integer (0-15), bits [3:0] = fraction (x/16)
; Displayed as decimal integer + '.' + hex nibble (exact x/16 representation)
; Examples: 0x5A → "5.A" (5 + 10/16 = 5.625), 0x0F → "0.F" (15/16)
; In:  A = Q4.4 value, D = output cursor
; Out: D = next output position
; Saves: A, B

io_q44_print:
        PUSH A
        PUSH B
        MOV B, A

        SHR A, 4
        CMP A, 10
        JC iq44_s
        PUSH A
        MOV A, 49
        MOV [D], A
        INC D
        POP A
        SUB A, 10
iq44_s: ADD A, 48
        MOV [D], A
        INC D

        MOV A, 46
        MOV [D], A
        INC D

        MOV A, B
        AND A, 0x0F
        CMP A, 10
        JC iq44_d
        ADD A, 55
        JMP iq44_w
iq44_d: ADD A, 48
iq44_w: MOV [D], A
        INC D

        POP B
        POP A
        RET
