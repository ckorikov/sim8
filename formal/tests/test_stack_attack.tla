--------------------------- MODULE test_stack_attack ---------------------------
(*
   Stack attack tests - stack overflow, underflow, stack smashing
*)

EXTENDS cpu_core

TestProgram == <<
    \* --- Test: Stack underflow attempt ---
    \* SP starts at 231, try to POP when stack is empty
    OP_POP, REG_A,            \* Should FAULT - stack is empty

    \* Unreachable
    OP_HLT
>>

\* Should fault with stack underflow
FaultsOnUnderflow == (state = "FAULT") => (A = ERR_STACK_UNDERFLOW)

\* Must terminate (not hang)
MustTerminate == <>(state \in {"HALTED", "FAULT"})

=============================================================================
