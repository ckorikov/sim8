--------------------------- MODULE test_invalid_code ---------------------------
(*
   Test invalid opcode handling and jump to instruction middle
*)

EXTENDS cpu_core

TestProgram == <<
    \* Test 1: Execute invalid opcode (9 is not assigned)
    9,                        \* addr 0: invalid opcode 9
    OP_HLT                    \* addr 1: unreachable
>>

\* Invalid opcode should FAULT
InvalidOpcodeFaults == (state = "FAULT") => (A = ERR_INVALID_OPCODE)

\* Must reach FAULT state
MustFault == <>(state = "FAULT")

=============================================================================
