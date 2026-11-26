; inference.asm — Tiny GPT (trans8) forward pass on pysim8 / arch=3
;
; Model (from /Users/ck/dev/2026-spring-efficient-ai/trans8):
;   d_model=6, n_heads=2, head_dim=3, d_ff=3, n_layers=2, vocab=4 (ABCD), T=9.
;
; Weights are bf16 (export_weights.py converts trans8/out/weights.json).
; Output: 9 ASCII chars on display cells [0xE8..0xF0].
;
; Page map:
;   0      code + stack + I/O
;   1..5   weight blob (1056 B)        — see weights.layout.txt
;   16     constants + parameter block + INPUT
;   17     activations: x, xn, qkv, attn_out
;   18     ffn buffers + logits + scratch
;
; Calling convention:
;   - All subroutines read/write a parameter block on page 16 (DP=16).
;   - DP is set to 16 at entry to each helper; restored by helpers that
;     temporarily change it.
;   - VU operations use absolute 16-bit addressing — DP does not affect them.

@page 0

main:
        MOV     DP, 16              ; param block / constants page

        CALL    embed               ; x[t] = tok_emb[INPUT[t]] + pos_emb[t]
        CALL    fwd_block0          ; forward through layer 0
        CALL    fwd_block1          ; forward through layer 1
        CALL    final_head          ; ln_f + head + argmax + display
        HLT

; ─────────────────────────────────────────────────────────────────
; embed: x[t,:] = tok_emb[INPUT[t]] + pos_emb[t]  for t = 0..8
;
; Reads INPUT (9 bytes) on page 16, writes 9 rows of 6 bf16 to x_buf.
; Uses VU for the 6-element copy + add per position.
; ─────────────────────────────────────────────────────────────────
embed:
        VSET    VL, 6
        MOV     C, 0                ; t (position index, 0..8)
.eloop:
        ; --- compute &tok_emb[INPUT[t]] = (page 1, off 0 + INPUT[t]*12) ---
        MOV     B, input
        ADD     B, C
        MOV     A, [B]              ; A = INPUT[t]  (token id 0..3)
        ; offset in tok_emb = A * 12 (each row is 6 bf16 = 12 B)
        MOV     B, A
        ADD     A, A
        ADD     A, A
        ADD     A, A                ; A = 8*tok_id
        ADD     A, B
        ADD     A, B
        ADD     A, B
        ADD     A, B                ; A = 12*tok_id  ← byte offset within tok_emb
        VSET    VA, {tok_emb_lbl}, A

        ; --- compute &pos_emb[t] = (page 1, off pos_emb_off + t*12) ---
        MOV     B, C                ; B = t
        ADD     B, B
        ADD     B, B
        ADD     B, B                ; B = 8t
        MOV     D, C
        ADD     B, D
        ADD     B, D
        ADD     B, D
        ADD     B, D                ; B = 12t
        ADD     B, pos_emb_off      ; B += 48
        VSET    VB, {pos_emb_lbl}, B

        ; --- &x_buf[t] (page 17, off t*12) ---
        MOV     D, C
        ADD     D, D
        ADD     D, D
        ADD     D, D                ; D = 8t
        MOV     A, C
        ADD     D, A
        ADD     D, A
        ADD     D, A
        ADD     D, A                ; D = 12t
        VSET    VC, {x_buf}, D

        VADD.BF VC, VA, VB          ; x[t] = tok_emb[id] + pos_emb[t]
        VWAIT
        ADD     C, 1
        CMP     C, 9
        JNZ     .eloop
        RET

; ─────────────────────────────────────────────────────────────────
; fwd_block0 / fwd_block1 — wrappers that load weight pointers for
; the appropriate layer into the param block, then dispatch to fwd_block.
; ─────────────────────────────────────────────────────────────────
fwd_block0:
        MOV     A, {ln1_w_0}
        MOV     [pp_ln_g_pg], A
        MOV     A, ln1_w_0_off
        MOV     [pp_ln_g_off], A
        MOV     A, {ln1_b_0}
        MOV     [pp_ln_b_pg], A
        MOV     A, ln1_b_0_off
        MOV     [pp_ln_b_off], A
        MOV     A, {qkv_w_0}
        MOV     [pp_qkv_pg], A
        MOV     A, qkv_w_0_off
        MOV     [pp_qkv_off], A
        MOV     A, {out_w_0}
        MOV     [pp_out_pg], A
        MOV     A, out_w_0_off
        MOV     [pp_out_off], A
        MOV     A, {ln2_w_0}
        MOV     [pp_ln2g_pg], A
        MOV     A, ln2_w_0_off
        MOV     [pp_ln2g_off], A
        MOV     A, {ln2_b_0}
        MOV     [pp_ln2b_pg], A
        MOV     A, ln2_b_0_off
        MOV     [pp_ln2b_off], A
        MOV     A, {ffu_w_0}
        MOV     [pp_ffu_pg], A
        MOV     A, ffu_w_0_off
        MOV     [pp_ffu_off], A
        MOV     A, {ffd_w_0}
        MOV     [pp_ffd_pg], A
        MOV     A, ffd_w_0_off
        MOV     [pp_ffd_off], A
        JMP     fwd_block

fwd_block1:
        MOV     A, {ln1_w_1}
        MOV     [pp_ln_g_pg], A
        MOV     A, ln1_w_1_off
        MOV     [pp_ln_g_off], A
        MOV     A, {ln1_b_1}
        MOV     [pp_ln_b_pg], A
        MOV     A, ln1_b_1_off
        MOV     [pp_ln_b_off], A
        MOV     A, {qkv_w_1}
        MOV     [pp_qkv_pg], A
        MOV     A, qkv_w_1_off
        MOV     [pp_qkv_off], A
        MOV     A, {out_w_1}
        MOV     [pp_out_pg], A
        MOV     A, out_w_1_off
        MOV     [pp_out_off], A
        MOV     A, {ln2_w_1}
        MOV     [pp_ln2g_pg], A
        MOV     A, ln2_w_1_off
        MOV     [pp_ln2g_off], A
        MOV     A, {ln2_b_1}
        MOV     [pp_ln2b_pg], A
        MOV     A, ln2_b_1_off
        MOV     [pp_ln2b_off], A
        MOV     A, {ffu_w_1}
        MOV     [pp_ffu_pg], A
        MOV     A, ffu_w_1_off
        MOV     [pp_ffu_off], A
        MOV     A, {ffd_w_1}
        MOV     [pp_ffd_pg], A
        MOV     A, ffd_w_1_off
        MOV     [pp_ffd_off], A
        ; fall through into fwd_block

fwd_block:
        ; LN1: xn = layernorm(x; pp_ln_g, pp_ln_b)
        ; ... matmul Q,K,V from xn
        ; ... attention → attn_out
        ; ... residual: x += attn_out  (via output projection then add)
        ; LN2: xn = layernorm(x; pp_ln2g, pp_ln2b)
        ; ... ffn_up, gelu, ffn_down → ffn_out
        ; ... residual: x += ffn_out
        ; (full implementation requires more code than fits in page 0;
        ;  this scaffold lays out the call structure)
        HLT                          ; placeholder — see roadmap below

final_head:
        HLT                          ; placeholder

; ═════════════════════════════════════════════════════════════════
; Page 16 — constants, parameter block, INPUT
; ═════════════════════════════════════════════════════════════════
@page 16
input:        DB 0, 1, 2, 3, 0, 0, 1, 2, 3   ; 9 token ids: ABCDA + ABCD

; FP constants (bf16) used by helpers
zero_bf:      DB 0.0_bf
one_bf:       DB 1.0_bf
neg_inf_bf:   DB -inf_bf
half_bf:      DB 0.5_bf
inv6_bf:      DB 0.16796875_bf      ; 1/6 ≈ 0.1680
inv_sqrt3_bf: DB 0.5773502588272095_bf
eps_bf:       DB 0.00001_bf

; Parameter block — overwritten by fwd_block0/1 for each layer.
; Each pointer = (page, offset) = 2 bytes.
pp_ln_g_pg:   DB 0
pp_ln_g_off:  DB 0
pp_ln_b_pg:   DB 0
pp_ln_b_off:  DB 0
pp_qkv_pg:    DB 0
pp_qkv_off:   DB 0
pp_out_pg:    DB 0
pp_out_off:   DB 0
pp_ln2g_pg:   DB 0
pp_ln2g_off:  DB 0
pp_ln2b_pg:   DB 0
pp_ln2b_off:  DB 0
pp_ffu_pg:    DB 0
pp_ffu_off:   DB 0
pp_ffd_pg:    DB 0
pp_ffd_off:   DB 0

; Compile-time labels for the weight blob — provided by export_weights.py
; (see weights.layout.txt). Defined as @page directives + labels below.

; ═════════════════════════════════════════════════════════════════
; Pages 1..5 — bf16 weight blob (1056 B). Labels match layout.
; ═════════════════════════════════════════════════════════════════
@page 1
tok_emb_lbl:
@include "weights.bin"

; Symbolic labels for offsets within the blob (set as constants below).
; pos_emb_off, ln1_w_0_off, etc., are page-local offsets used by code.
; Their @page bases (e.g., {pos_emb_lbl}) are derived from the labels.
;
; Since @include splits the blob across pages 1..5, we re-anchor each
; tensor with a symbolic label using @page, offset directives so callers
; can compose (page, off) at assembly time.

; (See README — these labels are added with @page <p>, <off> blocks; in
; the current scaffold they are wired up via export_weights.py output.)

@page 1, 48
pos_emb_lbl:
; pos_emb_off is just 48 (within page 1)

; The remaining tensor labels (ln1_w_0, ..., head_lbl) are stitched in
; via included include-shim file generated by export_weights.py.
@include "weights_labels.inc"

; ═════════════════════════════════════════════════════════════════
; Page 17 — activations
; ═════════════════════════════════════════════════════════════════
@page 17
x_buf:        DB 0, 0
@page 17, 108
xn_buf:       DB 0, 0
@page 17, 216
; remaining 40 B unused

@page 18
qkv_buf:      DB 0, 0           ; 9 × 18 bf16 = 324 B (spans page 18+19)

@page 20
attn_out_buf: DB 0, 0           ; 9 × 6 bf16 = 108 B
@page 20, 108
ffn_h_buf:    DB 0, 0           ; 9 × 3 bf16 = 54 B
@page 20, 162
ffn_out_buf:  DB 0, 0           ; 9 × 6 bf16 = 108 B (spills 14 B → page 21)

@page 21, 14
logits_buf:   DB 0, 0           ; 9 × 4 bf16 = 72 B

; Constants for offsets used by code
; pos_emb_off = 48
; (other offsets resolved at assembly time)
