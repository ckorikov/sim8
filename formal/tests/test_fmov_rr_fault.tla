--------------------------- MODULE test_fmov_rr_fault ---------------------------
(*
   FMOV_RR format mismatch triggers ERR_FP_FORMAT.

   FPM for FHA (fmt=1, float16, pos=0): 1
   FPM for BFA (fmt=2, bfloat16, pos=0): 2
   Different formats -> FAULT(ERR_FP_FORMAT).
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV_RR FHA, BFA  (fmt=1 vs fmt=2 -> format mismatch)
    OP_FMOV_RR, 1, 2,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
