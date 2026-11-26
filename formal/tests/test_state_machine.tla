--------------------------- MODULE test_state_machine ---------------------------
(*
   Test state machine invariants - state transitions
*)

EXTENDS cpu_core

TestProgram == <<
    \* Simple program that halts
    OP_MOV_RC, REG_A, 42,
    OP_MOV_RC, REG_B, 43,
    OP_ADD_RR, REG_A, REG_B,
    OP_HLT
>>

\* State is always valid
ValidTransition ==
    state \in {"IDLE", "RUNNING", "HALTED", "FAULT"}

\* Once halted, registers have expected values
HaltedStable == (state = "HALTED") =>
    (A = 85 /\ B = 43)  \* 42 + 43 = 85

\* Initial state is IDLE, then transitions to RUNNING
InitialOrRunning == (step_count = 0) => (state \in {"IDLE", "RUNNING"})

\* Step count non-negative
StepCountNonNegative == step_count >= 0

=============================================================================
