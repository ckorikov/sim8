--------------------------- MODULE test_instruction_props ---------------------------
(*
   Test instruction-specific invariants
*)

EXTENDS cpu_core

TestProgram == <<
    \* Set up flags first with an arithmetic operation
    OP_MOV_RC, REG_A, 255,
    OP_ADD_RC, REG_A, 1,      \* A = 0, Z = TRUE, C = TRUE

    \* MOV should preserve flags
    OP_MOV_RC, REG_B, 42,     \* Z and C should still be TRUE

    \* JMP should preserve flags
    OP_JMP, 12,               \* Jump to next instruction, flags unchanged

    \* CMP should not modify registers
    OP_MOV_RC, REG_C, 100,
    OP_MOV_RC, REG_D, 100,
    OP_CMP_RR, REG_C, REG_D,  \* Z = TRUE (equal), C = FALSE

    \* Verify C and D unchanged after CMP
    OP_HLT
>>

\* After ADD overflow: Z and C should be TRUE
AfterAddFlags == (IP = 6) => (Z = TRUE /\ C_flag = TRUE)

\* After MOV: flags preserved
MovPreservesFlags == (IP = 9) => (Z = TRUE /\ C_flag = TRUE)

\* After CMP: Z is TRUE (100 - 100 = 0)
CmpSetsZero == (state = "HALTED") => (Z = TRUE)

\* CMP preserves register values
CmpPreservesValues == (state = "HALTED") => (C = 100 /\ D = 100)

=============================================================================
