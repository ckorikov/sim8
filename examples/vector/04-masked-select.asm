; 04-masked-select.asm — Attention mask: zero out scores below threshold
;
; output[i] = scores[i] >= 40 ? scores[i] : 0
; Result: [50, 0, 80, 0, 90, 0, 70, 40]

@page 1
scores:    DB 50, 10, 80, 30, 90, 5, 70, 40
threshold: DB 0, 0, 0, 0, 0, 0, 0, 0   ; filled via VMOV
zeros:     DB 0, 0, 0, 0, 0, 0, 0, 0   ; filled via VMOV
mask:      DB 0, 0, 0, 0, 0, 0, 0, 0   ; VCMP output

@page 0
        VSET VL, 8

        ; ── Prepare constant vectors ─────────────────
        VSET VC, threshold
        VFILL.U VC, 40
        VSET VC, zeros
        VFILL.U VC, 0
        VWAIT

        ; ── Build mask: mask[i] = (scores[i] >= 40) ──
        VSET VA, scores
        VSET VB, threshold
        VSET VM, mask
        VCMP.U.GE VM, VA, VB
        VWAIT

        ; ── Apply: scores[i] = mask[i] ? scores[i] : 0 ─
        VSET VA, scores
        VSET VB, zeros
        VSET VM, mask
        VSEL.U VA, VM, VB
        VWAIT

        ; result at scores: [50, 0, 80, 0, 90, 0, 70, 40]
        HLT
