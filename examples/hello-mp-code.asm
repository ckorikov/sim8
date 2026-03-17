; Multi-page example: loader on page 0, data on page 1, print fn on page 2
;
; Interface contract:
;   Page 1: null-terminated string starts at offset 0
;   Page 2: print fn starts at offset 0, fits in 32 bytes
;           Calling convention: B=data_page, C=str_offset, D=output_port

print:                   ; overlay slot — print fn will be copied here at runtime
        JMP loader

@page 0, 32              ; reserve offsets 0-31 for the overlay

loader:
        ; Copy 32 bytes from page 2 offset 0 → print slot (page 0 offset 0)
        ; Jump targets in print fn are page-2-relative, so slot must be at offset 0
        MOV C, 0
        MOV D, 0
.copy:
        CMP D, 32
        JE .run
        MOV DP, 2
        MOV A, [C]
        MOV DP, 0
        MOV [D], A
        INC C
        INC D
        JMP .copy

.run:
        MOV B, 1               ; data page
        MOV C, 0               ; string offset
        MOV D, 232             ; output port
        CALL print
        HLT

@page 1
        DB "Hello World!"
        DB 0

@page 2
; print(B: data_page, C: str_offset, D: output_port)
        PUSH A
.loop:  MOV DP, B
        MOV A, [C]
        CMP A, 0
        JZ .done
        MOV DP, 0
        MOV [D], A
        INC C
        INC D
        JMP .loop
.done:  MOV DP, 0
        POP A
        RET
