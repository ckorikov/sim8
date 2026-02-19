--------------------------- MODULE test_fp_control ---------------------------
(*
   FP control flow: FSCFG sets FPCR, FCFG reads it back, FCLR clears FPSR.
   Sets FPCR to 1 (RM=01=RTZ) via MOV+FSCFG.
   FPCR only holds RM (bits [1:0]); bits [7:2] are reserved and masked to 0.
*)

EXTENDS cpu_core

TestProgram == <<
    \* Load 1 (RTZ) into A
    OP_MOV_RC, REG_A, 1,
    \* FSCFG A — write A to FPCR (only RM bits kept)
    OP_FSCFG, 0,
    \* FCFG B — read FPCR -> B
    OP_FCFG, 1,
    \* FCLR — clear FPSR
    OP_FCLR,
    \* FSTAT C — read FPSR -> C (should be 0)
    OP_FSTAT, 2,
    OP_HLT
>>

\* After FSCFG(1), FPCR = 1 (RTZ)
FPCRSetCorrectly == state = "HALTED" => FPCR_reg = 1

\* After FCFG B, B = FPCR = 1
FCFGReadsCorrectly == state = "HALTED" => B = 1

\* After FCLR + FSTAT C, C = 0
FPSRClearedCorrectly == state = "HALTED" => C = 0

=============================================================================
