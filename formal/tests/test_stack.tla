--------------------------- MODULE test_stack ---------------------------
(*
   Stack test: PUSH, POP, CALL, RET
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 42,
    OP_PUSH_R, REG_A,
    OP_MOV_RC, REG_A, 0,
    OP_POP, REG_A,
    OP_CALL, 16,
    OP_MOV_RC, REG_B, 99,
    OP_HLT,
    OP_MOV_RC, REG_C, 77,
    OP_RET
>>

=============================================================================
