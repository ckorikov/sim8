; io_hex_print — uint8 as two hex digits "XX"
; In:  A = uint8, D = output cursor
; Out: D = next output position
; Saves: A, B

io_hex_print:
        PUSH A
        PUSH B
        MOV B, A
        SHR A, 4
        CALL ihn_nb
        MOV A, B
        AND A, 0x0F
        CALL ihn_nb
        POP B
        POP A
        RET

ihn_nb:
        CMP A, 10
        JC ihn_d
        ADD A, 55
        JMP ihn_w
ihn_d:  ADD A, 48
ihn_w:  MOV [D], A
        INC D
        RET
