--------------------------- MODULE test_fp_format_fault ---------------------------
(*
   FP format fault: invalid FPM byte -> FAULT(ERR_FP_FORMAT=12)
   FPM byte 5 has fmt=5 which is a reserved 4-bit format (E2M1).
   fmt=5 triggers ValidateFPM to return ERR_FP_FORMAT.
   Note: fmt=3 (E4M3) and fmt=4 (E5M2) are active OFP8 formats in v2.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FABS, 5,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
