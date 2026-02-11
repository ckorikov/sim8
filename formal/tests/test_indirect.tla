--------------------------- MODULE test_indirect ---------------------------
(*
   Indirect addressing: MOV reg, [reg], offset encoding
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_A, 100,    \* A = 100 (base address)
    OP_MOV_AC, 100, 42,       \* memory[100] = 42
    OP_MOV_RI, REG_B, 0,      \* B = memory[A+0] = memory[100] = 42
    OP_HLT
>>

\* After indirect load, B should be 42
IndirectLoadCorrect == (state = "HALTED") => (B = 42)

=============================================================================
