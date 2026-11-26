; 02-relu.asm — ReLU activation: output[i] = max(0, input[i])
;
; INT8 signed input, negative values clamped to 0.
; Result: [0, 10, 0, 42, 0, 0, 127, 0]

@page 1
input:  DB -5, 10, -20, 42, 0, -128, 127, -1
output: DB 0, 0, 0, 0, 0, 0, 0, 0    ; scratch for result (8 × int8)

@page 0
        VSET VL, 8
        VSET VA, input
        VSET VC, output

        VMAX.I VC, VA, 0
        VWAIT
        HLT
