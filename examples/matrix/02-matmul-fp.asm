; 02-matmul-fp.asm — 2×2 FP32 matrix multiply: C = A @ B
;
; C = [[4.0, 2.0],[10.0, 4.0]]  (FP32 at mat_c)

@page 1

; mat_a (2×2) row-major — FP32
;         col:      0       1
mat_a:    DB   1.0_f, 2.0_f   ; row 0
          DB   3.0_f, 4.0_f   ; row 1

; mat_b (2×2) row-major — FP32
;         col:      0       1
mat_b:    DB   2.0_f, 0.0_f   ; row 0
          DB   1.0_f, 1.0_f   ; row 1

; mat_c (2×2) row-major — FP32 output
mat_c:    DB   0.0_f, 0.0_f   ; row 0
          DB   0.0_f, 0.0_f   ; row 1

@page 0
        MSHAPE  2, 2, 2         ; M=2, N=2, K=2

        MSET    MA, mat_a
        MSET    MB, mat_b
        MSET    MC, mat_c

        MMUL.F  MC, MA, MB
        MWAIT
        HLT
