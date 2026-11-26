--------------------------- MODULE test_fp_rr_cmp ---------------------------
(*
   Reg-reg compare: FCMP_RR with float16.
   Both FHA and FHB are +0.0 (FA_reg=0), so FCMP_RR should set Z=TRUE, C=FALSE.
   Then JZ jumps to HLT (success). If Z were FALSE, JNZ would fault.
   FPM for FHA (fmt=1, pos=0): 1
   FPM for FHB (fmt=1, pos=1): 9
*)

EXTENDS cpu_core

TestProgram == <<
    \* FCMP_RR FHA, FHB — compare +0.0 == +0.0 (3 bytes: 0,1,2)
    OP_FCMP_RR, 1, 9,
    \* JZ to HLT (2 bytes: 3,4 — target=offset 6)
    OP_JZ, 6,
    \* Should not reach here — invalid opcode as sentinel (offset 5)
    255,
    \* HLT at offset 6
    OP_HLT
>>

\* Must halt (not fault)
ReachesHalted == <>(state = "HALTED")

=============================================================================
