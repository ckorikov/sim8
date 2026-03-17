; Multi-page data example
; Writes Hello World to the output using data on page 1
;
; Same as hello.asm but data lives on a separate page,
; freeing page 0 for code (no JMP to skip over data).

start:
        MOV B, {hello}       ; Page of data
        MOV C, hello         ; Offset of data
        MOV D, 232           ; Point to output
        CALL print
        HLT                  ; Stop execution

print:                       ; print(B:page, C:*from, D:*to)
        PUSH A
        PUSH DP

.loop:
        MOV DP, B            ; Switch to data page
        MOV A, [C]           ; Read byte
        CMP A, 0             ; Check if end
        JZ .done
        MOV DP, 0            ; Switch to page 0
        MOV [D], A           ; Write to output
        INC C
        INC D
        JMP .loop

.done:
        POP DP
        POP A
        RET

@page 1
hello:
        DB "Hello World!"
        DB 0
