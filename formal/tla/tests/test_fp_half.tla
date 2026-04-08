--------------------------- MODULE test_fp_half ---------------------------
(*
   FP multi-format test: float16 and bfloat16 at pos=0.
   FPM for float16 pos=0: fmt=1 -> FPM=1
   FPM for bfloat16 pos=0: fmt=2 -> FPM=2
   Note: pos=1 causes TLC int32 overflow (bit_off=16, value*65536 > 2^31).
   Memory at addr 240 is 0 (init), which encodes +0.0 in any FP format.
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV FHA, [240] — load +0.0 (float16, FPM=1)
    OP_FMOV_FA, 1, 240,
    \* FABS FHA (FPM=1)
    OP_FABS, 1,
    \* FMOV BFA, [240] — load +0.0 (bfloat16, FPM=2)
    OP_FMOV_FA, 2, 240,
    \* FNEG with bfloat16 (FPM=2) — neg of +0.0 = -0.0
    OP_FNEG, 2,
    OP_HLT
>>

\* FA_reg stays non-negative
FANonNeg == FA_reg >= 0

=============================================================================
