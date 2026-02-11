--------------------------- MODULE test_fault_codes ---------------------------
(*
   Test that fault codes are correctly set
*)

EXTENDS cpu_core

TestProgram == <<
    \* Push many values to cause stack overflow
    OP_MOV_RC, REG_A, 42,
    OP_PUSH_R, REG_A,
    OP_PUSH_R, REG_A,
    OP_PUSH_R, REG_A,
    OP_HLT
>>

\* Fault code is valid when fault occurs
FaultCodeInvariant == (state = "FAULT") =>
    (A \in {ERR_DIV_ZERO, ERR_STACK_OVERFLOW, ERR_STACK_UNDERFLOW,
            ERR_INVALID_REG, ERR_PAGE_BOUNDARY, ERR_INVALID_OPCODE})

\* Running state means F flag is false
RunningMeansNoFault == (state = "RUNNING") => (F = FALSE)

\* Halted means no fault
HaltedMeansNoFault == (state = "HALTED") => (F = FALSE)

=============================================================================
