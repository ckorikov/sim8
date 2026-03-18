; io.common — shared helpers for sim8 I/O library
; Provides: io_puts, io_itoa, io_dot2d, io_s_nan, io_s_inf
; Req: DP = 0

io_s_nan: DB "NaN"
          DB 0
io_s_inf: DB "Inf"
          DB 0

; io_puts — print null-terminated string
; In:  C = ptr to string, D = output cursor
; Out: D = next output position
; Trashes: A
io_puts:
        MOV A, [C]
        CMP A, 0
        JZ io_puts_r
        MOV [D], A
        INC C
        INC D
        JMP io_puts
io_puts_r:
        RET

; io_itoa — print uint8 as decimal, no leading zeros
; In:  A = uint8 (0-255), D = output cursor
; Out: D = next output position
; Trashes: A, B, C
io_itoa:
        MOV B, A
        MOV C, 0
io_ia_lp:
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
        JNZ io_ia_lp
io_ia_pr:
        POP A
        MOV [D], A
        INC D
        DEC C
        JNZ io_ia_pr
        RET

; io_dot2d — print ".XY" (decimal point + two digits)
; In:  C = tens digit (0-9), A = units digit (0-9), D = cursor
; Out: D = next output position
; Trashes: A, B
io_dot2d:
        MOV [D], 46
        INC D
        MOV B, C
        ADD B, 48
        MOV [D], B
        INC D
        ADD A, 48
        MOV [D], A
        INC D
        RET
