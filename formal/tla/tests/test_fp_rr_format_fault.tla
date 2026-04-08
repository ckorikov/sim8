--------------------------- MODULE test_fp_rr_format_fault ---------------------------
(*
   Reg-reg format mismatch: FADD_RR with dst=FHA (fmt=1) and src=BFA (fmt=2).
   Different formats -> ERR_FP_FORMAT fault.
   FPM for FHA (fmt=1, pos=0): 1
   FPM for BFA (fmt=2, pos=0): 2
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FADD_RR, 1, 2,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
