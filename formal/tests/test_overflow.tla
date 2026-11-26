--------------------------- MODULE test_overflow ---------------------------
(*
   Overflow/underflow edge cases
*)

EXTENDS cpu_core

TestProgram == <<
    \* Test overflow: 255 + 1 = 0 with carry
    OP_MOV_RC, REG_A, 255,
    OP_ADD_RC, REG_A, 1,      \* A should be 0, C_flag should be TRUE

    \* Test underflow: 0 - 1 = 255 with carry (borrow)
    OP_MOV_RC, REG_B, 0,
    OP_SUB_RC, REG_B, 1,      \* B should be 255, C_flag should be TRUE

    OP_HLT
>>

\* After ADD 255+1: result wraps to 0
OverflowWraps == (IP = 5) => (A = 0)

\* After SUB 0-1: result wraps to 255
UnderflowWraps == (IP = 11) => (B = 255)

\* Carry set on overflow (after ADD at IP=5, before next instruction)
CarryOnOverflow == (IP = 5) => C_flag

=============================================================================
