--------------------------- MODULE test_fp_fmadd_basic ---------------------------
(*
   FMADD direct: dst = src * mem[addr] + dst, float16.
   Both FHA and FHB are +0.0 (FA_reg=0), mem[240] = 0 (+0.0).
   FMADD FHA, FHB, [240] -> FHA = FHB * mem[240] + FHA = 0*0+0 = oracle.
   FPM for FHA (fmt=1, pos=0): 1
   FPM for FHB (fmt=1, pos=1): 9
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMADD_A FHA, FHB, [240]
    OP_FMADD_A, 1, 9, 240,
    OP_HLT
>>

\* FA_reg stays non-negative
FANonNeg == FA_reg >= 0

=============================================================================
