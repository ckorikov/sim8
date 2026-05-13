--------------------------- MODULE test_mset_fault_reg ---------------------------
(*
   Test: MSET with mreg=6 (> 5) raises ERR_INVALID_REG at decode.
   Encoding: [188, 6, 0, 1]  — MSET_IMM16, mreg=6 (invalid: only 0–5 valid)
*)
EXTENDS cpu_core

TestProgram == <<
    188, 6, 0, 1,   \* MSET mreg=6, 0x0100 → ERR_INVALID_REG
    0               \* HLT (unreachable)
>>

GotFault    == <>(state = "FAULT")
FaultIsReg  == (state = "FAULT") => (A = ERR_INVALID_REG)

=============================================================================
