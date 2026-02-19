--------------------------- MODULE test_fp_fmadd_fault ---------------------------
(*
   FMADD format mismatch: dst=FHA (fmt=1) and src=BFA (fmt=2).
   Different formats -> ERR_FP_FORMAT fault.
   FPM for FHA (fmt=1, pos=0): 1
   FPM for BFA (fmt=2, pos=0): 2
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FMADD_A, 1, 2, 240,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
