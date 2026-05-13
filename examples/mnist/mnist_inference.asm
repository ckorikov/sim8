; mnist_inference.asm — MNIST digit classification on sim8 VU
;
; Model: Linear(784,16) → ReLU → Linear(16,10) → argmax
; Weights: fp16, loaded via @include from binary files
; Input:   drawn on the simulator pixel pad
; Output:  predicted digit (0-9) written to console I/O
;
; Pad setup: configure simulator pad → page 111, offset 0, size 28

; ═══════════════════════════════════════════════════════════════
; Code (page 0)
; ═══════════════════════════════════════════════════════════════

@page 0

        ; ── Read pad input → fp16 (normalize uint8 0–255 to 0.0–1.0) ──
        VSET VL, 784
        VSET VA, pad_input      ; uint8 pixels from drawing pad (page 111)
        VSET VC, input
        VCVT.H.U VC, VA         ; convert 784 uint8 → fp16
        VWAIT

        VSET VL, 784
        VSET VA, input
        VSET VB, inv255         ; scalar pointer: fp16 value of 1/255
        VSET VC, input
        VMUL.H.vs VC, VA, VB    ; normalize: input[i] *= 1/255
        VWAIT

        ; ── Zero scratch buffers ──────────────────────────
        VSET VL, 16
        VSET VC, hidden_out
        VMOV.H VC, 0                ; zero 16 fp16 values
        VWAIT

        VSET VL, 10
        VSET VC, logits
        VMOV.H VC, 0                ; zero 10 fp16 values
        VWAIT

        ; ── Hidden layer: 16 dot products (784→16) ───────
        VSET VL, 784
        VSET VA, hw                 ; weight rows (auto-advances by 1568B)
        VSET VC, hidden_out         ; output (auto-advances by 2B per VDOT)

        MOV A, 16
h_loop:
        VSET VB, input              ; reset input pointer each iteration
        VDOT.H VC, VA, VB
        VWAIT
        SUB A, 1
        JNZ h_loop

        ; ── Add hidden bias ───────────────────────────────
        VSET VL, 16
        VSET VA, hidden_out
        VSET VB, hb
        VSET VC, hidden_out
        VADD.H VC, VA, VB
        VWAIT

        ; ── ReLU ──────────────────────────────────────────
        VSET VA, hidden_out
        VSET VC, hidden_out
        VMAX.H VC, VA, 0
        VWAIT

        ; ── Output layer: 10 dot products (16→10) ────────
        VSET VL, 16
        VSET VA, ow                 ; weight rows (auto-advances by 32B)
        VSET VC, logits             ; output (auto-advances by 2B per VDOT)

        MOV A, 10
o_loop:
        VSET VB, hidden_out         ; reset hidden pointer each iteration
        VDOT.H VC, VA, VB
        VWAIT
        SUB A, 1
        JNZ o_loop

        ; ── Add output bias ──────────────────────────────
        VSET VL, 10
        VSET VA, logits
        VSET VB, ob
        VSET VC, logits
        VADD.H VC, VA, VB
        VWAIT

        ; ── Argmax: find max logit via VMAX reduction ────
        VSET VA, logits
        VSET VC, max_val
        VMAX.H VC, VA              ; reduction: max of 10 elements
        VWAIT

        ; ── Scalar scan: find index of max ───────────────
        MOV DP, {logits}
        FMOV.H FHA, [max_val]      ; FHA = max logit value
        MOV B, 0                    ; B = best index
        MOV C, logits               ; C = current offset in page

argmax:
        FMOV.H FHB, [C]            ; load logits[i]
        FCMP.H FHB, FHA            ; compare with max
        JZ found                    ; if equal → found
        ADD B, 1
        ADD C, 2                    ; next fp16 (2 bytes)
        CMP B, 10
        JNZ argmax

found:
        ; B = predicted digit (0-9)
        ; Output to console: digit + ASCII '0'
        MOV A, B
        ADD A, 48                   ; '0' = 48
        MOV DP, 0                   ; console I/O is on page 0
        MOV [0xE8], A               ; write to console I/O
        HLT

; ═══════════════════════════════════════════════════════════════
; Data pages — weights (loaded from binary files)
; ═══════════════════════════════════════════════════════════════

; Hidden layer weights: [16, 784] fp16 = 25088 bytes
; Pages 1-98 (auto-split by @include cross-page)
@page 1
hw:
@include "hidden_weight.bin"

; Hidden layer bias: [16] fp16 = 32 bytes
; Page 99
@page 99
hb:
@include "hidden_bias.bin"

; Output layer weights: [10, 16] fp16 = 320 bytes
; Pages 100-101 (auto-split)
@page 100
ow:
@include "output_weight.bin"

; Output layer bias: [10] fp16 = 20 bytes
@page 102
ob:
@include "output_bias.bin"

; ═══════════════════════════════════════════════════════════════
; Input image: 784 fp16 values = 1568 bytes (pages 103-108)
; Filled at runtime by the pad-reading code above.
; ═══════════════════════════════════════════════════════════════

@page 103
input:                              ; written at runtime by VCVT from pad

; ═══════════════════════════════════════════════════════════════
; Scratch buffers (page 110)
; ═══════════════════════════════════════════════════════════════

@page 110
hidden_out:                         ; 16 fp16 = 32 bytes (offsets 0x00-0x1F)

@page 110, 32
logits:                             ; 10 fp16 = 20 bytes (offsets 0x20-0x33)

@page 110, 52
max_val:                            ; 1 fp16 = 2 bytes  (offsets 0x34-0x35)

@page 110, 54
inv255:
DB 0.003921569_h                    ; 1/255 as fp16 — normalization factor for pad pixels

; ═══════════════════════════════════════════════════════════════
; Pad input (page 111) — 28×28 UINT8 pixels
; Configure simulator pad: page 111, offset 0, size 28
; ═══════════════════════════════════════════════════════════════

@page 111
pad_input:                          ; 784 bytes (28×28), written by mouse drawing
