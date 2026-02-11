--------------------------- MODULE test_sp_relative ---------------------------
(*
   SP-relative addressing ignores DP (always page 0).
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_DP, 5,        \* DP = 5 (non-zero page)
    OP_PUSH_C, 42,               \* push 42: mem[231] = 42, SP = 230
    OP_MOV_RI, REG_A, 12,        \* A = mem[SP+1]: regaddr = (1<<3)|4 = 12
                                  \*   reg=SP(4), offset=+1, addr=231, page 0
    OP_HLT
>>

\* SP-relative read should get 42 despite DP = 5
SPRelativeIgnoresDP == (state = "HALTED") => (A = 42)

=============================================================================
