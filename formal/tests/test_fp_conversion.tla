--------------------------- MODULE test_fp_conversion ---------------------------
(*
   FP conversion: FITOF and FFTOI with float16.
   FITOF: A (=42) -> FHA (float16 pos=0)
   FFTOI: FHA -> B
   FPM=1 means fmt=1 (float16), pos=0, phys=0.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 42,
    \* FITOF FHA, A (FPM=1, GPR=0)
    OP_FITOF, 1, 0,
    \* FFTOI B, FHA (FPM=1, GPR=1)
    OP_FFTOI, 1, 1,
    OP_HLT
>>

\* After FFTOI, B is a valid byte
BInRange == state = "HALTED" => B \in BYTE

=============================================================================
