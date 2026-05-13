; mnist_inference.asm — MNIST digit classification on sim8 VU
; Model: Linear(784,16) → ReLU → Linear(16,10) → argmax
; Weights: fp16. Pad: page 111, offset 0, size 28.

@page 0

        ; normalize: uint8 → fp16, ×(1/255)
        VSET VL, 784
        VSET VA, pad_input
        VSET VC, input
        VCVT.H.U VC, VA

        VSET VA, input
        VSET VB, inv255
        VSET VC, input
        VMUL.H.vs VC, VA, VB

        ; hidden layer: 16 × VDOT(784)
        VSET VA, hw                 ; auto-advances +1568B per VDOT
        VSET VC, hidden_out         ; auto-advances +2B per VDOT

        MOV A, 16
h_loop:
        VSET VB, input
        VDOT.H VC, VA, VB
        SUB A, 1
        JNZ h_loop

        ; bias + ReLU
        VSET VL, 16
        VSET VA, hidden_out
        VSET VB, hb
        VSET VC, hidden_out
        VADD.H VC, VA, VB

        VSET VA, hidden_out
        VSET VB, zero_h             ; vi mode broken for FP — use .vs with mem zero
        VSET VC, hidden_out
        VMAX.H.vs VC, VA, VB

        ; output layer: 10 × VDOT(16)
        VSET VL, 16
        VSET VA, ow                 ; auto-advances +32B per VDOT
        VSET VC, logits             ; auto-advances +2B per VDOT

        MOV A, 10
o_loop:
        VSET VB, hidden_out
        VDOT.H VC, VA, VB
        SUB A, 1
        JNZ o_loop

        ; bias
        VSET VL, 10
        VSET VA, logits
        VSET VB, ob
        VSET VC, logits
        VADD.H VC, VA, VB

        ; argmax — VWAIT: CPU reads max_val written by VU
        VSET VA, logits
        VSET VC, max_val
        VMAX.H VC, VA
        VWAIT

        MOV DP, {logits}
        FMOV.H FHA, [max_val]
        MOV B, 0
        MOV C, logits

argmax:
        FMOV.H FHB, [C]
        FCMP.H FHB, FHA
        JZ found
        ADD B, 1
        ADD C, 2
        CMP B, 10
        JNZ argmax

found:
        MOV A, B
        ADD A, 48                   ; ASCII '0'
        MOV DP, 0
        MOV [0xE8], A               ; console I/O
        HLT

inv255: DB 0.003921569_h
zero_h: DB 0.0_h

@page 1
hw:
@include "hidden_weight.bin"

@page 99
hb:
@include "hidden_bias.bin"

@page 100
ow:
@include "output_weight.bin"

@page 102
ob:
@include "output_bias.bin"

@page 103
input:

@page 110
hidden_out:

@page 110, 32
logits:

@page 110, 52
max_val:

@page 111
pad_input:
