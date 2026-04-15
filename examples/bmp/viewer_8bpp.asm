; BMP Viewer (8bpp) — displays an 8-bit grayscale BMP on the pad via VMOV.U
;
; Square image, width must be a multiple of 4 (stride == width).
; Reads bottom-up BMP natively: starts from last pixel row, works backward.
; Set pad to match image size before running.
;
; Memory layout:
;   page 0        — code + variables
;   pages 1-16    — pad (up to 64×64)
;   pages 17+     — BMP file data

; ── Pad (display memory) ─────────────────────────────────

@page 1
pad:

; ── Header ───────────────────────────────────────────────

@page 18
header:
header_signature:       DB 0,0      ; 'BM' = 0x42, 0x4D
header_file_size:       DB 0,0,0,0  ; file size
                        DB 0,0,0,0  ; reserved
header_data_offset:     DB 0,0,0,0  ; pixel data offset

; ── InfoHeader (BITMAPINFOHEADER, 40 bytes) ──────────────

info_header:
info_header_size:        DB 0,0,0,0  ; header size (= 40)
info_header_width:       DB 0,0,0,0  ; image width

; ── BMP data (overlay from offset 0) ─────────────────────

@page 18, 0
@include "img_8bpp.bmp"

; ── Main ─────────────────────────────────────────────────

@page 0

        MOV DP, {header}
        MOV C, [info_header_width]
        MOV D, C

        PUSH D
        DEC D
        CALL mul16              ; A:B = (height - 1) * width

        PUSH A
        PUSH B
        MOV A, [header_data_offset]
        MOV B, [header_data_offset + 1]
        POP C
        ADD A, C
        JNC .lo_nc
        INC B
.lo_nc: POP C
        ADD B, C
        ADD B, {header}
        MOV DP, 0
        MOV [v_src], B
        MOV [v_src + 1], A
        MOV [v_dst], {pad}
        MOV [v_dst + 1], 0

        MOV DP, {header}
        MOV C, [info_header_width]
        POP D
        VSET VL, C

        MOV DP, 0
        CALL vmov_row
        DEC D

.row:   MOV A, [v_dst]
        MOV B, [v_dst + 1]
        CALL add16
        MOV [v_dst], A
        MOV [v_dst + 1], B

        MOV A, [v_src + 1]
        SUB A, C
        MOV [v_src + 1], A
        JNC .src_nc
        MOV A, [v_src]
        DEC A
        MOV [v_src], A
.src_nc:
        CMP D, 0
        JZ halt

        CALL vmov_row
        DEC D
        JMP .row

halt:   HLT

; ── Functions ────────────────────────────────────────────

vmov_row:
        MOV A, [v_src]
        MOV B, [v_src + 1]
        VSET VA, A, B
        MOV A, [v_dst]
        MOV B, [v_dst + 1]
        VSET VB, A, B
        VMOV.U VB, VA
        RET

add16:
        PUSH A
        MOV A, B
        ADD A, C
        MOV B, A
        POP A
        JNC .nc
        INC A
.nc:    RET

mul16:
        MOV A, 0
        MOV B, 0
.loop:  CMP D, 0
        JZ .done
        CALL add16
        DEC D
        JMP .loop
.done:  RET

; ── Variables (after code, same page 0) ──────────────────

v_src:   DB 0, 0
v_dst:   DB 0, 0
