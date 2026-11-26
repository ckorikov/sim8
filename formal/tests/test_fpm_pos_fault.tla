--------------------------- MODULE test_fpm_pos_fault ---------------------------
(*
   FPM position out-of-range triggers ERR_FP_FORMAT.

   Rules (from spec/fp.md):
   - fmt=0 (FP32):  only pos=0 valid;  pos=1 -> fault
   - fmt=1 (FP16):  pos in {0,1} valid; pos=2 -> fault

   FPM encoding: (phys << 6) | (pos << 3) | fmt
   FPM = 8  -> phys=0, pos=1, fmt=0  (FP32 pos=1 -- invalid)
   FPM = 17 -> phys=0, pos=2, fmt=1  (FP16 pos=2 -- invalid)

   We test the FP32 case: FABS with FPM=8.
*)

EXTENDS cpu_core

TestProgram == <<
    \* FABS with FPM=8 (fmt=0, pos=1) -> FAULT(ERR_FP_FORMAT)
    OP_FABS, 8,
    OP_HLT
>>

\* Must reach FAULT with ERR_FP_FORMAT
FaultIsFPFormat == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
