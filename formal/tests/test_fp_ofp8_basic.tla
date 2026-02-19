--------------------------- MODULE test_fp_ofp8_basic ---------------------------
(*
   OFP8 load/unary/classify: E4M3 (fmt=3) and E5M2 (fmt=4) at pos=0.
   FPM for E4M3 FQA (fmt=3, pos=0): 3
   FPM for E5M2 FQA (fmt=4, pos=0): 4
   Memory at addr 240 is 0 (init) = +0.0 in any FP format (1 byte for OFP8).
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV FQA.E4M3, [240] — load +0.0 (1-byte access)
    OP_FMOV_FA, 3, 240,
    \* FABS FQA.E4M3 — no-op on +0.0
    OP_FABS, 3,
    \* FMOV FQA.E5M2, [240] — aliases same FQA bits
    OP_FMOV_FA, 4, 240,
    \* FCLASS B, FQA.E5M2 — +0.0 -> B = 1 (ZERO)
    OP_FCLASS, 4, 1,
    \* FNEG FQA.E5M2 — +0.0 -> -0.0 (0x80)
    OP_FNEG, 4,
    \* FCLASS C, FQA.E5M2 — -0.0 -> C = 65 (ZERO | NEG)
    OP_FCLASS, 4, 2,
    OP_HLT
>>

FANonNeg            == FA_reg >= 0
ClassifyZeroE5M2    == state = "HALTED" => B = 1
ClassifyNegZeroE5M2 == state = "HALTED" => C = 65
FPSRUnchanged       == state = "HALTED" => FPSR_reg = 0

=============================================================================
