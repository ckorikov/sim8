; perf_vmov_v.asm — Performance: VMOV.U at different VL values
;
; Window = 16 bytes. VWAIT drain counted in CPU cycles.
;
; VL=1:  setup(4) + issue(1) + vwait_issue(1) + drain(1) = 7 cycles
; VL=4:  same = 7 cycles (fits in 1 window)
; VL=16: same = 7 cycles (fits in 1 window)
; VL=17: setup(4) + issue(1) + vwait_issue(1) + drain(2) = 8 cycles
; VL=32: setup(4) + issue(1) + vwait_issue(1) + drain(2) = 8 cycles
; VL=33: setup(4) + issue(1) + vwait_issue(1) + drain(3) = 9 cycles
;
; Scalar equivalent for VL=16: 16 × (MOV A,[C]; MOV [D],A; INC C; INC D) = 16 × 4 = 64 cycles + loop overhead

@page 1
src:    DB 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16
        DB 17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32
        DB 33
dst:    DB 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
        DB 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
        DB 0

@page 0
    ; Test: VL=16 (1 window)
    VSET VL, 16
    VSET VA, src
    VSET VB, dst
    VMOV.U VB, VA
    VWAIT
    HLT
