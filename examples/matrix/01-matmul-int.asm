; 01-matmul-int.asm — 2×2 UINT8 matrix multiply: C = A @ B
;
; C = [[19,22],[43,50]]  (UINT32 at mat_c)

@page 1

; mat_a (2×2) row-major
;          col:  0  1
mat_a:     DB    1, 2   ; row 0
           DB    3, 4   ; row 1

; mat_b (2×2) row-major
;          col:  0  1
mat_b:     DB    5, 6   ; row 0
           DB    7, 8   ; row 1

; mat_c (2×2) row-major — UINT32 output
mat_c:     DB 0,0,0,0, 0,0,0,0   ; row 0
           DB 0,0,0,0, 0,0,0,0   ; row 1

@page 0
        MSHAPE  2, 2, 2

        MSET    MA, mat_a
        MSET    MB, mat_b
        MSET    MC, mat_c

        MMUL.U  MC, MA, MB
        MWAIT
        HLT
