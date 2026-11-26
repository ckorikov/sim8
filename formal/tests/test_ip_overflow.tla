--------------------------- MODULE test_ip_overflow ---------------------------
(*
   Test: IP overflow triggers FAULT(ERR_PAGE_BOUNDARY)
   Place a 3-byte instruction at address 254 — needs bytes 254,255,256
   which exceeds page 0. Should FAULT before executing.
*)

EXTENDS cpu_core

TestProgram ==
    <<OP_JMP, 254>>                          \* bytes 0-1: jump to 254
    \o [i \in 1..252 |-> 0]                  \* bytes 2-253: padding
    \o <<OP_ADD_RC, REG_A, 1>>               \* bytes 254-256: ADD A, 1 (would overflow)

\* The machine must FAULT (not HALT) due to IP overflow
MustFault == (state \in {"HALTED", "FAULT"}) => (state = "FAULT")

\* Fault code must be ERR_PAGE_BOUNDARY
FaultIsPageBoundary == (state = "FAULT") => (A = ERR_PAGE_BOUNDARY)

=============================================================================
