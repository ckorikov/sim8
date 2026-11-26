--------------------------- MODULE test_fpm_phys_fault ---------------------------
(*
   FPM reserved physical register (phys=2) triggers ERR_FP_FORMAT.

   FPM encoding: (phys << 6) | (pos << 3) | fmt
   FPM = 128 = 0b10000000 -> phys=2, pos=0, fmt=0
   Only phys 0 and 1 are valid; phys=2 must fault.
*)

EXTENDS cpu_core

TestProgram == <<
    \* FABS with FPM=128 (phys=2) -> FAULT(ERR_FP_FORMAT)
    OP_FABS, 128,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
