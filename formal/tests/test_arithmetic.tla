--------------------------- MODULE test_arithmetic ---------------------------
(*
   Test for arithmetic operations with overflow/underflow
*)

EXTENDS cpu_core

TestProgram == <<
    \* Test ADD overflow with carry
    OP_MOV_RC, REG_A, 200,
    OP_MOV_RC, REG_B, 100,
    OP_ADD_RR, REG_A, REG_B,  \* A = 300 % 256 = 44, C = TRUE

    \* Test SUB underflow with carry
    OP_MOV_RC, REG_C, 10,
    OP_MOV_RC, REG_D, 20,
    OP_SUB_RR, REG_C, REG_D,  \* C = 10 - 20 = -10 + 256 = 246, C = TRUE

    \* Test MUL overflow
    OP_MOV_RC, REG_A, 20,
    OP_MUL_C, 15,             \* A = 20 * 15 = 300 % 256 = 44, C = TRUE

    \* Test DIV
    OP_MOV_RC, REG_A, 100,
    OP_MOV_RC, REG_B, 7,
    OP_DIV_R, REG_B,          \* A = 100 / 7 = 14

    OP_HLT
>>

\* After ADD overflow: A = 44
AddOverflowCorrect == (IP = 9) => (A = 44)

\* After SUB underflow: C = 246
SubUnderflowCorrect == (IP = 18) => (C = 246)

\* Final DIV result
DivResultCorrect == (state = "HALTED") => (A = 14)

=============================================================================
