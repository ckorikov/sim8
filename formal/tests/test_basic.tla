--------------------------- MODULE test_basic ---------------------------
(*
   Basic test: MOV, ADD, SUB, INC, DEC, HLT
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 10,
    OP_MOV_RC, REG_B, 5,
    OP_ADD_RR, REG_A, REG_B,
    OP_SUB_RC, REG_A, 3,
    OP_INC, REG_A,
    OP_DEC, REG_A,
    OP_HLT
>>

=============================================================================
