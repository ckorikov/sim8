; 05-mlp-two-layer.asm — Two-layer MLP: 4 → 2 (ReLU) → 1
;
; UINT8. W1=[[1,1,0,0],[0,0,1,1]], W2=[1,2], b2=5, x=[5,3,2,1]
; hidden = [8, 3], output = 1*8 + 2*3 + 5 = 19

@page 1
w1_r0:  DB 1, 1, 0, 0
w1_r1:  DB 0, 0, 1, 1
x:      DB 5, 3, 2, 1
w2:     DB 1, 2
b2:     DB 5
temp:   DB 0, 0, 0, 0        ; scratch (shared, max 4 bytes)
hidden: DB 0                  ; h[0]
h1:     DB 0                  ; h[1]
output: DB 0                  ; final result

@page 0
        ; ── Layer 1: hidden = W1 * x (VL=4) ──────────
        VSET VL, 4

        MOV A, {w1_r0}
        MOV B, w1_r0
        MOV C, {hidden}
        MOV D, hidden
        CALL dot

        MOV A, {w1_r1}
        MOV B, w1_r1
        MOV C, {h1}
        MOV D, h1
        CALL dot

        VWAIT

        ; ── Layer 2: output = dot(W2, hidden) (VL=2) ──
        VSET VL, 2

        MOV A, {w2}
        MOV B, w2
        MOV C, {output}
        MOV D, output
        CALL dot_h

        VWAIT

        ; ── Bias: output += b2 ────────────────────────
        VSET VL, 1
        VSET VA, output
        VSET VB, b2
        VSET VC, output
        VADD.U VC, VA, VB
        VWAIT

        HLT

; ── dot: VC = sum(VA * VB), src1=x ────────────────────
; in:  A:B = weights addr, C:D = output addr, VL set by caller
dot:
        VSET VA, A, B
        VSET VB, x
        VSET VC, temp
        VMUL.U VC, VA, VB
        VSET VA, temp
        VSET VC, C, D
        VADD.U VC, VA
        RET

; ── dot_h: VC = sum(VA * VB), src1=hidden ─────────────
; in:  A:B = weights addr, C:D = output addr, VL set by caller
dot_h:
        VSET VA, hidden
        VSET VB, A, B
        VSET VC, temp
        VMUL.U VC, VA, VB
        VSET VA, temp
        VSET VC, C, D
        VADD.U VC, VA
        RET
