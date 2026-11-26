--------------------------- MODULE test_dp_paging ---------------------------
(*
   DP register paging: writes to page 1 should not affect page 0.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_DP, 1,        \* DP = 1 (page 1)
    OP_MOV_RC, REG_B, 50,        \* B = 50
    OP_MOV_IC, 1, 42,            \* [B+0] = 42, writes to addr 1*256+50 = 306
    OP_MOV_RI, REG_A, 1,         \* A = mem[B+0] on page 1 = 42
    OP_MOV_RC, REG_DP, 0,        \* DP = 0 (page 0)
    OP_MOV_RI, REG_C, 1,         \* C = mem[B+0] on page 0 = mem[50] = 0
    OP_HLT
>>

\* Read from page 1 should return the written value
PagedWriteCorrect == (state = "HALTED") => (A = 42)

\* Read from page 0 at same offset should be unaffected
Page0Separate == (state = "HALTED") => (C = 0)

=============================================================================
