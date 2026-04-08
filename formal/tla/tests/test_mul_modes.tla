--------------------------- MODULE test_mul_modes ---------------------------
(*
   MUL/DIV with register indirect and direct address modes
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 6,         \* A = 6
    OP_MOV_RC, REG_B, 100,       \* B = 100 (base addr)
    OP_MOV_AC, 100, 7,           \* mem[100] = 7
    OP_MUL_I, 1,                 \* MUL [B+0]: A = 6 * 7 = 42
    OP_MOV_RR, REG_C, REG_A,    \* C = 42
    OP_MOV_RC, REG_A, 8,         \* A = 8
    OP_MUL_A, 100,               \* MUL [100]: A = 8 * 7 = 56
    OP_MOV_RR, REG_D, REG_A,    \* D = 56
    OP_MOV_RC, REG_A, 20,        \* A = 20
    OP_MOV_AC, 100, 4,           \* mem[100] = 4
    OP_DIV_I, 1,                 \* DIV [B+0]: A = 20 / 4 = 5
    OP_MOV_AC, 100, 3,           \* mem[100] = 3
    OP_MOV_RC, REG_A, 15,        \* A = 15
    OP_DIV_A, 100,               \* DIV [100]: A = 15 / 3 = 5
    OP_HLT
>>

\* After MUL [B], C should hold 42
MulIndirectCorrect == (state = "HALTED") => (C = 42)

\* After MUL [100], D should hold 56
MulDirectCorrect == (state = "HALTED") => (D = 56)

\* After both DIV operations, A should be 5
DivResult == (state = "HALTED") => (A = 5)

=============================================================================
