--------------------------- MODULE test_associativity ---------------------------
(*
   Test associativity of bitwise operations: (A op B) op C = A op (B op C)
*)

EXTENDS cpu_core

TestProgram == <<
    \* Test XOR associativity: (A ^ B) ^ C = A ^ (B ^ C)
    \* A=0x12, B=0x34, C=0x56

    \* Compute (A ^ B) ^ C
    OP_MOV_RC, REG_A, 18,     \* A = 0x12
    OP_MOV_RC, REG_B, 52,     \* B = 0x34
    OP_XOR_RR, REG_A, REG_B,  \* A = 0x12 ^ 0x34 = 0x26
    OP_MOV_RC, REG_C, 86,     \* C = 0x56
    OP_XOR_RR, REG_A, REG_C,  \* A = 0x26 ^ 0x56 = 0x70

    \* Compute A ^ (B ^ C) in D
    OP_MOV_RC, REG_B, 52,     \* B = 0x34
    OP_MOV_RC, REG_C, 86,     \* C = 0x56
    OP_XOR_RR, REG_B, REG_C,  \* B = 0x34 ^ 0x56 = 0x62
    OP_MOV_RC, REG_D, 18,     \* D = 0x12
    OP_XOR_RR, REG_D, REG_B,  \* D = 0x12 ^ 0x62 = 0x70

    OP_HLT
>>

\* Both methods give same result
XorAssocResult == (state = "HALTED") => (A = D)

\* Result should be 0x70 = 112
CorrectResult == (state = "HALTED") => (A = 112 /\ D = 112)

=============================================================================
