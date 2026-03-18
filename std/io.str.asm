; io.str.asm
; API: print_str
; In: A=ptr to zero-terminated DB string, D=cursor | Out: D=next
; Req: DP=0
;
; Example:
;   @include "std/io.str.asm"
;   JMP start
; text: DB "Hello", 0
;
; start: MOV A, text
;        MOV D, 232
;        CALL print_str
;        HLT

print_str:
        PUSH A
        PUSH C
        MOV C, A
string_copy_loop:
        MOV A, [C]
        CMP A, 0
        JZ string_copy_done
        MOV [D], A
        INC C
        INC D
        JMP string_copy_loop
string_copy_done:
        POP C
        POP A
        RET
