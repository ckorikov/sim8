---------------------------- MODULE test_mfstat ----------------------------
(*
   Test: MFSTAT copies MFPSR to GPR (opcode 190).
   MFPSR starts at 0; MFSTAT copies it to A → A=0.
   Also verifies MFCLR (opcode 191) leaves MFPSR=0 and state proceeds.
*)
EXTENDS cpu_core

TestProgram == <<
    190, 0,         \* MFSTAT A  → A = MFPSR = 0
    191,            \* MFCLR     → MFPSR = 0
    190, 1,         \* MFSTAT B  → B = MFPSR = 0
    0               \* HLT
>>

MustHalt   == <>(state = "HALTED")
AIsZero    == state = "HALTED" => A = 0
BIsZero    == state = "HALTED" => B = 0

=============================================================================
