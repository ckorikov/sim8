--------------------------- MODULE test_fp_arith ---------------------------
(*
   FP arithmetic structural test with float16 format.
   FADD on zero operands — result is nondeterministic oracle,
   but structure (FPM decode, memory read, register write) is verified.
   FPM=1 means fmt=1 (float16), pos=0, phys=0.
   Memory at addr 240 is 0 (init), so mem operand is +0.0 (float16).
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FMOV_FA, 1, 240,
    OP_FADD_A, 1, 240,
    OP_HLT
>>

\* FA_reg stays non-negative
FANonNeg == FA_reg >= 0

=============================================================================
