--------------------------- MODULE test_demorgan ---------------------------
(*
   Test De Morgan's Laws and bitwise properties
*)

EXTENDS cpu_core

TestProgram == <<
    \* Test De Morgan: ~(A & B) = ~A | ~B
    \* Using A=0xAA (170), B=0x55 (85)
    \* A & B = 0x00, ~(A & B) = 0xFF
    \* ~A = 0x55, ~B = 0xAA, ~A | ~B = 0xFF
    OP_MOV_RC, REG_A, 170,    \* A = 0xAA
    OP_MOV_RC, REG_B, 85,     \* B = 0x55
    OP_AND_RR, REG_A, REG_B,  \* A = 0xAA & 0x55 = 0x00
    OP_NOT, REG_A,            \* A = ~0x00 = 0xFF

    \* Compute ~A | ~B separately
    OP_MOV_RC, REG_C, 170,    \* C = 0xAA
    OP_NOT, REG_C,            \* C = ~0xAA = 0x55
    OP_MOV_RC, REG_D, 85,     \* D = 0x55
    OP_NOT, REG_D,            \* D = ~0x55 = 0xAA
    OP_OR_RR, REG_C, REG_D,   \* C = 0x55 | 0xAA = 0xFF

    OP_HLT
>>

\* De Morgan result: A should equal C (both 0xFF)
DeMorganResult == (state = "HALTED") => (A = C)

\* Both should be 255
BothAre255 == (state = "HALTED") => (A = 255 /\ C = 255)

\* Intermediate: ~0xAA = 0x55
NotAAIs55 == (IP > 15) => (C = 85 \/ IP > 18)

=============================================================================
