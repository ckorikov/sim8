; test_block_copy.asm — Test VU block_copy: copy 8 bytes between pages
;
; Copies page 1 offset 0 (8 bytes) to page 2 offset 0.
; Expected: page 2 bytes 0-7 = 0xAA, 0xBB, 0xCC, 0xDD, 0x11, 0x22, 0x33, 0x44

    JMP start
    @include "libs/std/sys.loader.asm"

@page 1
data:   DB 0xAA, 0xBB, 0xCC, 0xDD, 0x11, 0x22, 0x33, 0x44

@page 0
start:
    ; block_copy: A:B=src, C:D=dst, VL=length
    MOV A, 1            ; src high = page 1
    MOV B, 0            ; src low = offset 0
    MOV C, 2            ; dst high = page 2
    MOV D, 0            ; dst low = offset 0
    VSET VL, 8
    CALL block_copy
    HLT
