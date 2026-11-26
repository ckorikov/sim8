; 01-dot-product.asm — Single neuron: output = dot(weights, inputs)
;
; VMUL + VADD reduction. Result wraps: 2*10+3*20+1*30+4*40 = 270 mod 256 = 14

@page 1
weights:  DB 2, 3, 1, 4
inputs:   DB 10, 20, 30, 40
product:  DB 0, 0, 0, 0      ; scratch: VMUL result (4 × uint8)
result:   DB 0                ; scratch: reduction result (1 × uint8)

@page 0
        VSET VL, 4
        VSET VA, weights
        VSET VB, inputs
        VSET VC, product

        VMUL.U VC, VA, VB
        VSET VA, product
        VSET VC, result
        VADD.U VC, VA

        VWAIT
        HLT
