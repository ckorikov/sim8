--------------------------- MODULE test_adversarial ---------------------------
(*
   Adversarial/edge-case tests - unusual programming patterns
   Tests architecture robustness against "creative" code
*)

EXTENDS cpu_core

TestProgram == <<
    \* --- Test 1: Self-modifying code ---
    \* Write HLT (0) to address 20, then jump there
    OP_MOV_AC, 20, 0,         \* mem[20] = 0 (HLT)
    OP_JMP, 20,               \* Jump to self-written HLT

    \* This code is unreachable if self-mod works
    OP_MOV_RC, REG_A, 255,    \* Should not execute
    OP_HLT
>>

\* Self-modifying code should work - we halt at address 20
SelfModWorks == (state = "HALTED") => (IP = 20)

\* A should remain 0 (never executed MOV A, 255)
UnreachableNotExecuted == (state = "HALTED") => (A = 0)

=============================================================================
