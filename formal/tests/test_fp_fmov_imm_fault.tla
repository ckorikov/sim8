--------------------------- MODULE test_fp_fmov_imm_fault ---------------------------
(*
   FMOV Immediate format mismatch fault test.
   Op 161 (imm8) requires fmt in {3,4} (8-bit OFP8).
   Using FPM=1 (fmt=1, float16) with op 161 -> FAULT(ERR_FP_FORMAT).
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV_FI8 with 16-bit format FPM=1 (fmt=1, float16) -> format mismatch
    OP_FMOV_FI8, 1, 60,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
