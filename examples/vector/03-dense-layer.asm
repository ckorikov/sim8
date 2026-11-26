; 03-dense-layer.asm — Dense layer: y = W*x + b (2 neurons, 4 inputs)
;
; W = [[1,2,3,4],[5,6,7,8]], x = [1,1,1,1], b = [10,20]
; y[0] = 1+2+3+4 + 10 = 20, y[1] = 5+6+7+8 + 20 = 46

@page 1
w_row0: DB 1, 2, 3, 4
w_row1: DB 5, 6, 7, 8
x:      DB 1, 1, 1, 1
bias:   DB 10, 20
temp:   DB 0, 0, 0, 0        ; scratch for multiply result
y:      DB 0                  ; neuron 0 output
y1:     DB 0                  ; neuron 1 output

@page 0
        VSET VL, 4

        ; y[0] = dot(W[0], x)
        MOV A, {w_row0}
        MOV B, w_row0
        MOV C, {y}
        MOV D, y
        CALL dot

        ; y[1] = dot(W[1], x)
        MOV A, {w_row1}
        MOV B, w_row1
        MOV C, {y1}
        MOV D, y1
        CALL dot

        VWAIT

        ; y += bias
        VSET VL, 2
        VSET VA, y
        VSET VB, bias
        VSET VC, y
        VADD.U VC, VA, VB
        VWAIT
        HLT

; ── dot: VC = sum(VA * VB) ────────────────────────────
; in:  A:B = weights addr, C:D = output addr, VL = width
;      VB already set to x by invariant? No — set here.
; out: result at C:D, VU queue has 2 commands
dot:
        VSET VA, A, B             ; weights
        VSET VB, x          ; input vector
        VSET VC, temp    ; scratch
        VMUL.U VC, VA, VB
        VSET VA, temp
        VSET VC, C, D             ; output
        VADD.U VC, VA
        RET
