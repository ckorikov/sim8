--------------------------- MODULE test_div_zero ---------------------------
(*
   Test division by zero - including self-division A/A when A=0
*)

EXTENDS cpu_core

TestProgram == <<
    \* A starts at 0, divide A by A (0/0)
    OP_DIV_R, REG_A,          \* A / A where A=0 -> FAULT
    OP_HLT                    \* unreachable
>>

\* Division by zero should FAULT
DivZeroFaults == (state = "FAULT") => (A = ERR_DIV_ZERO)

\* Must reach FAULT state
MustFault == <>(state = "FAULT")

=============================================================================
