; 03-gemm-accumulate.asm — GEMM with M/N/K tiling: C = A @ B via 2x2x2 tiles
;
; A (6x4) @ B (4x6) = C (6x6). Tile size 2 on every axis,
; so the tile grid is 3x3 output tiles, each accumulated from K_tile=2 inner steps.
;
; Inputs A/B are FP16 (.H); C is FP32 (4 B/elem) per MU output rules.
;
; Storage is "tiled": each 2x2 sub-block lives contiguously (row-major within
; tile), tiles themselves laid out:
;   A: row-major over (mi, ki)              — 6 tiles, 8 B/tile (4 x FP16)
;   B: column-major over (ki, ni)           — 6 tiles, 8 B/tile (ki runs fastest)
;   C: row-major over (mi, ni)              — 9 tiles, 16 B/tile (4 x FP32)
;
; B's column-major-of-K-tiles ordering lets MMAD's auto-increment
; (MA += M*K*2, MB += K*N*2) walk the inner K loop without re-MSET of MA/MB.
; MC has no auto-increment, so a single MSET MC per (mi, ni) suffices —
; both K-tile MMADs accumulate into the same C tile.
;
; A logical (6x4):           B logical (4x6):
;    1  2  3  4               1 1 2 2 3 3
;    5  6  7  8               1 1 2 2 3 3
;    9 10 11 12               4 4 5 5 6 6
;   13 14 15 16               4 4 5 5 6 6
;   17 18 19 20
;   21 22 23 24
;
; C = A @ B (6x6), as FP32:
;    31  31  41  41  51  51
;    71  71  97  97 123 123
;   111 111 153 153 195 195
;   151 151 209 209 267 267
;   191 191 265 265 339 339
;   231 231 321 321 411 411

@page 1
; A — 6 tiles of 8 bytes (4 x FP16), row-major over (mi, ki)
mat_a:  DB  1.0_h,  2.0_h,  5.0_h,  6.0_h     ; tile (mi=0, ki=0)
        DB  3.0_h,  4.0_h,  7.0_h,  8.0_h     ; tile (mi=0, ki=1)
        DB  9.0_h, 10.0_h, 13.0_h, 14.0_h     ; tile (mi=1, ki=0)
        DB 11.0_h, 12.0_h, 15.0_h, 16.0_h     ; tile (mi=1, ki=1)
        DB 17.0_h, 18.0_h, 21.0_h, 22.0_h     ; tile (mi=2, ki=0)
        DB 19.0_h, 20.0_h, 23.0_h, 24.0_h     ; tile (mi=2, ki=1)

@page 2
; B — 6 tiles of 8 bytes (4 x FP16), column-major over (ki, ni)  [ki runs fastest]
mat_b:  DB 1.0_h, 1.0_h, 1.0_h, 1.0_h         ; tile (ki=0, ni=0)
        DB 4.0_h, 4.0_h, 4.0_h, 4.0_h         ; tile (ki=1, ni=0)
        DB 2.0_h, 2.0_h, 2.0_h, 2.0_h         ; tile (ki=0, ni=1)
        DB 5.0_h, 5.0_h, 5.0_h, 5.0_h         ; tile (ki=1, ni=1)
        DB 3.0_h, 3.0_h, 3.0_h, 3.0_h         ; tile (ki=0, ni=2)
        DB 6.0_h, 6.0_h, 6.0_h, 6.0_h         ; tile (ki=1, ni=2)

@page 3
; C — 9 tiles of 16 bytes (4 x FP32), row-major over (mi, ni)
mat_c:  DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f
        DB 0.0_f, 0.0_f, 0.0_f, 0.0_f

@page 0
        MSHAPE 2, 2, 2

        MOV C, 0                  ; C = mi (M-tile index, 0..2)
m_loop:
        MOV D, 0                  ; D = ni (N-tile index, 0..2)
n_loop:
        ; MC = mat_c + (mi*3 + ni) * 16
        MOV A, C
        MUL 3
        ADD A, D
        SHL A, 4
        MOV B, {mat_c}
        MSET MC, B, A

        ; MA = mat_a + mi*16        (start of K-tile 0 for row mi; 8 B/tile * 2 K-tiles)
        MOV A, C
        SHL A, 4
        MOV B, {mat_a}
        MSET MA, B, A

        ; MB = mat_b + ni*16        (start of K-tile 0 for col ni)
        MOV A, D
        SHL A, 4
        MOV B, {mat_b}
        MSET MB, B, A

        MMAD.H MC, MA, MB         ; ki=0; auto-inc advances MA, MB to ki=1
        MMAD.H MC, MA, MB         ; ki=1; MC stays put → accumulates into same tile

        INC D
        CMP D, 3
        JC n_loop

        INC C
        CMP C, 3
        JC m_loop

        MWAIT
        HLT
