--------------------------- MODULE test_xor ---------------------------
(*
   XOR test: XOR A, A should zero the register
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 123,    \* A = 123
    OP_XOR_RR, REG_A, REG_A,  \* A = A XOR A = 0
    OP_MOV_RC, REG_B, 170,    \* B = 0xAA = 10101010
    OP_MOV_RC, REG_C, 85,     \* C = 0x55 = 01010101
    OP_XOR_RR, REG_B, REG_C,  \* B = 0xAA XOR 0x55 = 0xFF = 255
    OP_HLT
>>

\* XOR with self gives 0
XorSelfZero == (IP > 5) => (A = 0)

\* XOR 0xAA with 0x55 gives 0xFF
XorComplementFull == (state = "HALTED") => (B = 255)

=============================================================================
