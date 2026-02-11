--------------------------- MODULE test_bitwise_carry ---------------------------
(*
   Bitwise ops (AND, OR, XOR, NOT) must clear the carry flag.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 255,       \* A = 255
    OP_ADD_RC, REG_A, 1,         \* A = 0, C = TRUE (overflow)
    OP_MOV_RC, REG_A, 255,       \* A = 255
    OP_AND_RC, REG_A, 15,        \* A = 15, C = FALSE
    OP_MOV_RC, REG_A, 200,       \* A = 200
    OP_ADD_RC, REG_A, 100,       \* A = 44, C = TRUE (overflow)
    OP_OR_RC, REG_A, 0,          \* A = 44, C = FALSE
    OP_MOV_RC, REG_A, 255,       \* A = 255
    OP_ADD_RC, REG_A, 1,         \* A = 0, C = TRUE (overflow)
    OP_MOV_RC, REG_A, 15,        \* A = 15
    OP_XOR_RC, REG_A, 15,        \* A = 0, C = FALSE
    OP_MOV_RC, REG_A, 255,       \* A = 255
    OP_ADD_RC, REG_A, 1,         \* A = 0, C = TRUE (overflow)
    OP_MOV_RC, REG_A, 255,       \* A = 255
    OP_NOT, REG_A,               \* A = 0, C = FALSE
    OP_HLT
>>

\* Last op is NOT which clears carry; at HALTED C_flag must be FALSE
BitwiseClearsCarry == (state = "HALTED") => (C_flag = FALSE)

=============================================================================
