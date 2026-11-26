; test_loader.asm — Test sys.loader.asm with VU-accelerated copy
;
; Overlay writes 42 to page 3 offset 0, then returns.
; After copy_and_call, we verify the side effect.
; Expected: mem[0x300] = 42

    JMP start
    @include "libs/std/sys.loader.asm"

@page 2, 0x40
overlay:
    PUSH DP
    MOV DP, 3
    MOV A, 42
    MOV [0], A
    POP DP
    RET

@page 0
start:
    MOV A, 0x40
    MOV B, 0x60
    MOV C, 2
    MOV D, 1
    CALL copy_and_call
    HLT
