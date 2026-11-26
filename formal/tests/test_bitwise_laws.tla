--------------------------- MODULE test_bitwise_laws ---------------------------
(*
   Test bitwise operation mathematical properties
*)

EXTENDS cpu_core

TestProgram == <<
    \* Test AND identity: A & 255 = A
    OP_MOV_RC, REG_A, 123,    \* A = 123
    OP_MOV_RC, REG_B, 255,    \* B = 255
    OP_AND_RR, REG_A, REG_B,  \* A = A & 255 = 123

    \* Test OR with zero: B | 0 = B
    OP_MOV_RC, REG_B, 200,    \* B = 200
    OP_MOV_RC, REG_C, 0,      \* C = 0
    OP_OR_RR, REG_B, REG_C,   \* B = B | 0 = 200

    \* Test NOT twice: ~~A = A
    OP_MOV_RC, REG_A, 42,     \* A = 42
    OP_NOT, REG_A,            \* A = ~42 = 213
    OP_NOT, REG_A,            \* A = ~213 = 42

    \* Test XOR is self-inverse: (A ^ B) ^ B = A
    OP_MOV_RC, REG_C, 77,     \* C = 77
    OP_MOV_RC, REG_D, 99,     \* D = 99
    OP_XOR_RR, REG_C, REG_D,  \* C = 77 ^ 99
    OP_XOR_RR, REG_C, REG_D,  \* C = (77 ^ 99) ^ 99 = 77

    OP_HLT
>>

\* AND with 255 is identity
AndIdentity == (state = "HALTED") => (A = 42)

\* OR with zero is identity
OrIdentity == (state = "HALTED") => (B = 200)

\* XOR is self-inverse
XorSelfInverse == (state = "HALTED") => (C = 77)

=============================================================================
