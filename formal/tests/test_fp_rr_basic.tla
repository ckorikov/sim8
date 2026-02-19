--------------------------- MODULE test_fp_rr_basic ---------------------------
(*
   Reg-reg arithmetic: FADD_RR with float16.
   Load two float16 values via FMOV, then FADD_RR FHA, FHB.
   FPM for FHA (fmt=1, pos=0): 1
   FPM for FHB (fmt=1, pos=1): 9 (1 + 1*8)
   Memory at 240 is 0 (init) = +0.0.
   Note: pos=1 reads bits[31:16] of FA_reg. With 16-bit float16 values
   and FA_reg starting at 0, both halves are 0 (+0.0).
*)

EXTENDS cpu_core

TestProgram == <<
    \* Load +0.0 into FHA (float16, pos=0)
    OP_FMOV_FA, 1, 240,
    \* FADD_RR FHA, FHB — FHA += FHB (both +0.0)
    OP_FADD_RR, 1, 9,
    OP_HLT
>>

\* FA_reg stays non-negative
FANonNeg == FA_reg >= 0

=============================================================================
