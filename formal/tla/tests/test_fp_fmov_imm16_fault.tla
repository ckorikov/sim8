--------------------------- MODULE test_fp_fmov_imm16_fault ---------------------------
(*
   FMOV_FI16 (op 162) requires fmt in {1, 2} (16-bit formats: float16, bfloat16).
   Using FPM=0 (fmt=0, float32) with op 162 -> FAULT(ERR_FP_FORMAT).

   Encoding: FMOV_FI16 fpm, lo, hi  (4 bytes)
   FPM = 0 -> fmt=0 (float32, 32-bit) -- not compatible with 16-bit immediate
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV_FI16 with FPM=0 (fmt=0, float32) -> format mismatch
    OP_FMOV_FI16, 0, 0, 62,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
