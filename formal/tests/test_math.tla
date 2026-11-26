--------------------------- MODULE test_math ---------------------------
(*
   Math test: MUL, DIV, overflow
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 10,
    OP_MUL_C, 5,
    OP_DIV_C, 10,
    OP_MOV_RC, REG_A, 200,
    OP_ADD_RC, REG_A, 100,
    OP_MOV_RC, REG_A, 5,
    OP_SUB_RC, REG_A, 10,
    OP_HLT
>>

=============================================================================
