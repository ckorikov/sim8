--------------------------- MODULE test_jumps ---------------------------
(*
   Jump test: JZ, JNZ
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 5,
    OP_CMP_RC, REG_A, 5,
    OP_JZ, 10,
    OP_JMP, 0,
    OP_HLT
>>

=============================================================================
