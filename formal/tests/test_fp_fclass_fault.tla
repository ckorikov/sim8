--------------------------- MODULE test_fp_fclass_fault ---------------------------
(*
   FCLASS with invalid GPR (4) -> FAULT(ERR_INVALID_REG=4).
   FPM=1 is valid, but GPR=4 (SP) is not a valid target.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FCLASS, 1, 4,
    OP_HLT
>>

\* Must reach FAULT with ERR_INVALID_REG
FaultIsInvalidReg == state = "FAULT" => A = ERR_INVALID_REG

=============================================================================
