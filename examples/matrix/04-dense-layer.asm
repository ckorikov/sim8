; 04-dense-layer.asm — Dense layer: y = W @ x  (3 neurons, 4 inputs)
;
; y = [[30],[70],[110]]  (UINT32 LE at output)

@page 1

; weights (3×4) row-major — W[neuron, input]
;            col:   0    1    2    3
weights:  DB        1,   2,   3,   4   ; row 0
          DB        5,   6,   7,   8   ; row 1
          DB        9,  10,  11,  12   ; row 2

; inputs (4×1) col vector
;            col:  0
inputs:   DB       1   ; row 0
          DB       2   ; row 1
          DB       3   ; row 2
          DB       4   ; row 3

; output (3×1) — UINT32
output:   DB 0,0,0,0   ; row 0
          DB 0,0,0,0   ; row 1
          DB 0,0,0,0   ; row 2

@page 0
        MSHAPE  3, 1, 4         ; M=3, N=1, K=4

        MSET    MA, weights
        MSET    MB, inputs
        MSET    MC, output

        MMUL.U  MC, MA, MB
        MWAIT
        HLT
