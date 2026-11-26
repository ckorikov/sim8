--------------------------- MODULE test_bitwise ---------------------------
(*
   Bitwise operations test: AND, OR, XOR, NOT, SHL, SHR
   This test exposes stub implementations!
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 255,    \* A = 0xFF
    OP_AND_RC, REG_A, 255,    \* A = A AND 0xFF (should stay 255, not become 0!)
    OP_HLT
>>

\* This invariant WILL FAIL if AND is a stub (returns 0)
\* Correct AND: 255 AND 255 = 255, so A should be 255 after AND
\* Stub AND: always returns 0, so A = 0 after AND
AndNotStub == (IP > 5 /\ state = "RUNNING") => (A = 255)

=============================================================================
