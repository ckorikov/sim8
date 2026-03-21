; sys.loader.asm
; API: copy_and_call
; In: A=start addr, B=end addr, C=source page, D=backup page
; Out: all registers, DP, FA, FB restored
;
; Copies page0[A..B] to pageD[A..B] (backup),
; copies pageC[A..B] to page0[A..B] (load overlay),
; executes CALL to address A (overlay must end with RET),
; then restores original code and all saved state.
;
; Constraints:
;   - A <= B
;   - Region [A..B] must not overlap with copy_and_call code or stack
;   - Overlay code must maintain stack discipline (balanced PUSH/POP)
;
; Example:
;   JMP start
;   @include "libs/std/sys.loader.asm"
;
; start: MOV A, 0x40       ; overlay region start
;        MOV B, 0x60       ; overlay region end
;        MOV C, 2          ; load from page 2
;        MOV D, 1          ; backup to page 1
;        CALL copy_and_call
;        HLT

copy_and_call:
        ; --- Save all state ---
        PUSH A
        PUSH B
        PUSH C
        PUSH D
        PUSH DP
        SUB SP, 4
        FMOV.F [SP+1], FA
        SUB SP, 4
        FMOV.F [SP+1], FB
        ; Stack: [SP+9]=DP [SP+10]=D [SP+11]=C [SP+12]=B [SP+13]=A

        ; Phase 1: backup page0[A..B] → pageD[A..B]
        MOV C, 0
        CALL cac_copy

        ; Phase 2: load overlay pageC[A..B] → page0[A..B]
        ; A, B preserved by cac_copy; reload C (was 0 after Phase 1)
        MOV C, [SP+11]
        MOV D, 0
        CALL cac_copy

        ; Phase 3: execute overlay
        ; A preserved by cac_copy; DP=0 (dest of Phase 2)
        CALL A

        ; Phase 4: restore pageD[A..B] → page0[A..B]
        MOV A, [SP+13]
        MOV B, [SP+12]
        MOV C, [SP+10]
        MOV D, 0
        CALL cac_copy

        ; --- Restore all state ---
        FMOV.F FB, [SP+1]
        ADD SP, 4
        FMOV.F FA, [SP+1]
        ADD SP, 4
        POP DP
        POP D
        POP C
        POP B
        POP A
        RET

; Internal: copy mem[A..B] from page C to page D
; Preserves A, B, C. Clobbers DP.
cac_copy:
        PUSH A
        PUSH C
cac_copy_loop:
        MOV DP, [SP+1]
        MOV C, [A]
        MOV DP, D
        MOV [A], C
        CMP A, B
        JZ cac_copy_done
        INC A
        JMP cac_copy_loop
cac_copy_done:
        POP C
        POP A
        RET
