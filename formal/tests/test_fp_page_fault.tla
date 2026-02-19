--------------------------- MODULE test_fp_page_fault ---------------------------
(*
   FP page boundary fault: FMOV FHA, [255] — float16 needs 2 bytes
   255+2-1=256 > 255 -> FAULT(ERR_PAGE_BOUNDARY=5)
   FPM=1 means fmt=1 (float16), pos=0, phys=0.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FMOV_FA, 1, 255,
    OP_HLT
>>

\* Must fault with page boundary error
FaultIsPageBoundary == state = "FAULT" => A = ERR_PAGE_BOUNDARY

=============================================================================
