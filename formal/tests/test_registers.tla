--------------------------- MODULE test_registers ---------------------------
(*
   Test register encoding invariants
*)

EXTENDS cpu_core

TestProgram == <<
    \* Set each register to a unique value
    OP_MOV_RC, REG_A, 10,
    OP_MOV_RC, REG_B, 20,
    OP_MOV_RC, REG_C, 30,
    OP_MOV_RC, REG_D, 40,
    OP_MOV_RC, REG_SP, 200,
    OP_MOV_RC, REG_DP, 1,

    \* Copy via register codes
    OP_MOV_RR, REG_A, REG_B,  \* A = B = 20
    OP_MOV_RR, REG_C, REG_D,  \* C = D = 40

    OP_HLT
>>

\* Register values are correct after setup
RegistersSetCorrectly == (IP = 18) =>
    (A = 10 /\ B = 20 /\ C = 30 /\ D = 40)

\* After copies
CopiesCorrect == (state = "HALTED") =>
    (A = 20 /\ C = 40)

\* SP was modified
SPModified == (IP > 15) => (SP = 200 \/ IP > 21)

\* DP was modified
DPModified == (state = "HALTED") => (DP = 1)

=============================================================================
