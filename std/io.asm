; sim8 standard I/O library
;
; Usage:
;   @include "std/io.asm"           — all printers (requires page 0 space)
;   @include "std/io.int.asm"       — standalone: io_int_print
;   @include "std/io.hex.asm"       — standalone: io_hex_print
;   @include "std/io.str.asm"       — standalone: io_str_print
;   @include "std/io.q44.asm"       — standalone: io_q44_print
;
; Float printers require io.common.asm:
;   @include "std/io.common.asm"
;   @include "std/io.fp16.asm"      — io_fp16_print  (float16)
;   @include "std/io.fp32.asm"      — io_fp32_print  (float32)
;   @include "std/io.bf16.asm"      — io_bf16_print  (bfloat16)
;   @include "std/io.fp8e4.asm"     — io_fp8e4_print (OFP8 E4M3)
;   @include "std/io.fp8e5.asm"     — io_fp8e5_print (OFP8 E5M2)
;
; Convention: D = output cursor (caller sets D = 232 for display)

@include "io.common.asm"
@include "io.str.asm"
@include "io.int.asm"
@include "io.hex.asm"
@include "io.q44.asm"
@include "io.fp16.asm"
@include "io.fp32.asm"
@include "io.bf16.asm"
@include "io.fp8e4.asm"
@include "io.fp8e5.asm"
