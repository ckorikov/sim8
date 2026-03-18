; io_int_print — uint8 decimal, no leading zeros
; In:  A = uint8 (0-255), D = output cursor
; Out: D = next output position
; Saves: A, B, C

io_int_print:
        PUSH A
        PUSH B
        PUSH C
        MOV B, A
        MOV C, 0
iip_lp: MOV A, B
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
        JNZ iip_lp
iip_pr: POP A
        MOV [D], A
        INC D
        DEC C
        JNZ iip_pr
        POP C
        POP B
        POP A
        RET
