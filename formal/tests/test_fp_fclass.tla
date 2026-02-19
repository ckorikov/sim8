--------------------------- MODULE test_fp_fclass ---------------------------
(*
   FCLASS: classify float16 +0.0 -> GPR = 0x01.
   FA_reg = 0 (init) means FHA = +0.0.
   FCLASS FHA -> A: bit 0 (ZERO) = 1, bit 6 (NEG) = 0 -> result = 1.
   FPM for FHA (fmt=1, pos=0): 1
*)

EXTENDS cpu_core

TestProgram == <<
    \* FCLASS A, FHA (FPM=1, GPR=0)
    OP_FCLASS, 1, 0,
    OP_HLT
>>

\* After FCLASS of +0.0, A = 1 (ZERO bit)
ClassifyZero == state = "HALTED" => A = 1

=============================================================================
