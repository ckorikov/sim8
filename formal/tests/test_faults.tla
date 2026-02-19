--------------------------- MODULE test_faults ---------------------------
(*
   Fault test: Division by zero
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 100,
    OP_MOV_RC, REG_B, 0,
    OP_DIV_R, REG_B,
    OP_HLT
>>

FaultHasErrorCode == F => (A \in {1,2,3,4,5,6,12})

=============================================================================
