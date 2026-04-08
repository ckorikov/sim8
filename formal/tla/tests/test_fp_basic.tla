--------------------------- MODULE test_fp_basic ---------------------------
(*
   FP basic test: FMOV (load zero), FABS, FNEG, FSTAT, FCFG, FSCFG, FCLR, HLT
   Uses float16 format (fmt=1) to stay within TLC integer range.
   FPM=1 means fmt=1, pos=0, phys=0.
   Memory at addr 240 is 0 (init), which encodes +0.0 in any FP format.
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV FHA, [240] — load +0.0 from zero-initialized memory
    OP_FMOV_FA, 1, 240,
    \* FABS FHA (FPM=1) — abs of +0.0 = +0.0
    OP_FABS, 1,
    \* FNEG FHA (FPM=1) — neg of +0.0 = -0.0
    OP_FNEG, 1,
    \* FSCFG A (reg=0) — write A (=0) to FPCR
    OP_FSCFG, 0,
    \* FCFG A (reg=0) — read FPCR -> A
    OP_FCFG, 0,
    \* FSTAT A (reg=0) — read FPSR -> A
    OP_FSTAT, 0,
    \* FCLR — clear FPSR
    OP_FCLR,
    OP_HLT
>>

\* FCLR clears FPSR
FCLRClearsStatus == state = "HALTED" => FPSR_reg = 0

=============================================================================
