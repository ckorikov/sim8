; io_str_print — null-terminated string
; In:  C = ptr to string (page DP), D = output cursor
; Out: D = next output position
; Saves: A
; Req: DP = 0

io_str_print:
        PUSH A
isp_lp: MOV A, [C]
        CMP A, 0
        JZ isp_dn
        MOV [D], A
        INC C
        INC D
        JMP isp_lp
isp_dn: POP A
        RET
