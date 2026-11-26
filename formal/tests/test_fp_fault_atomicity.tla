--------------------------- MODULE test_fp_fault_atomicity ---------------------------
(*
   FAULT atomicity: Z and C flags are preserved when a FP format fault fires.

   Per spec/errors.md: "Flags Z and C retain their pre-fault values;
   only F (set to TRUE) and A (set to error code) are modified."

   Program:
     1. CMP_RR A, A  -> A==A: Z=TRUE, C=FALSE
     2. FABS FPM=5   -> fmt=5 (reserved) -> FAULT(ERR_FP_FORMAT)

   After fault: state=FAULT, A=12, Z=TRUE (preserved), C_flag=FALSE (preserved).
*)

EXTENDS cpu_core

TestProgram == <<
    \* CMP A, A -> Z=TRUE, C=FALSE (A=0, 0==0)
    OP_CMP_RR, REG_A, REG_A,
    \* FABS with FPM=5 (fmt=5, reserved) -> FAULT(ERR_FP_FORMAT=12)
    OP_FABS, 5,
    OP_HLT
>>

\* Z and C must survive the fault transition
FaultPreservesZC == state = "FAULT" =>
    (Z = TRUE /\ C_flag = FALSE /\ A = ERR_FP_FORMAT)

=============================================================================
