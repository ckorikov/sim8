; perf_vmov_s.asm — Scalar copy 16 bytes for comparison
; Expected: ~64+ cycles (MOV+MOV+INC+INC per byte × 16 + loop overhead)

@page 1
src:    DB 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16
dst:    DB 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0

@page 0
    MOV D, 1            ; DP = page 1
    MOV C, 0            ; i = 0
    MOV B, 16           ; count
.loop:
    MOV A, [C]          ; 2 ticks (mem)
    PUSH C
    ADD C, 16
    MOV [C], A          ; 2 ticks (mem)
    POP C
    INC C               ; 1 tick
    DEC B               ; 1 tick
    JNZ .loop           ; 2 ticks (mem)
    HLT
