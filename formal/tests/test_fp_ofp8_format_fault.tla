--------------------------- MODULE test_fp_ofp8_format_fault ---------------------------
(*
   OFP8 pos out of range: E4M3 pos=4 -> FAULT(ERR_FP_FORMAT=12).
   FPM 35 = 0*64 + 4*8 + 3 (fmt=3, pos=4). Valid OFP8 pos is 0-3.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FABS, 35,
    OP_HLT
>>

\* pos=4 for OFP8 must fault with ERR_FP_FORMAT
FaultIsOFP8PosOutOfRange == state = "FAULT" => A = ERR_FP_FORMAT

=============================================================================
