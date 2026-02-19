--------------------------- MODULE test_fp_ofp8_fclass ---------------------------
(*
   OFP8 FCLASS: E4M3 (fmt=3) zero/neg-zero classification.
   E4M3 has no Infinity and only one NaN pattern (0x7F/0xFF, always qNaN).
   FPM for E4M3 FQA (fmt=3, pos=0): 3
   FPM for E4M3 FQB (fmt=3, pos=1): 11
   FPM for E5M2 FQA (fmt=4, pos=0): 4
   Memory at addr 240 is 0 (init) = +0.0.
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV FQA.E4M3, [240] — load +0.0
    OP_FMOV_FA, 3, 240,
    \* FCLASS A, FQA.E4M3 — +0.0 -> A = 1 (ZERO)
    OP_FCLASS, 3, 0,
    \* FNEG FQA.E4M3 — +0.0 -> -0.0 (0x80)
    OP_FNEG, 3,
    \* FCLASS B, FQA.E4M3 — -0.0 -> B = 65 (ZERO | NEG)
    OP_FCLASS, 3, 1,
    \* FMOV FQB.E4M3, [240] — load into pos=1, FQA unchanged
    OP_FMOV_FA, 11, 240,
    \* FMOV FQA.E5M2, [240] — aliases FQA bits, overwrites -0.0
    OP_FMOV_FA, 4, 240,
    \* FCLASS C, FQA.E5M2 — +0.0 -> C = 1 (ZERO)
    OP_FCLASS, 4, 2,
    OP_HLT
>>

FANonNeg         == FA_reg >= 0
E4M3ZeroClass    == state = "HALTED" => A = 1
E4M3NegZeroClass == state = "HALTED" => B = 65
E5M2ZeroClass    == state = "HALTED" => C = 1

\* E4M3 has no Inf and no sNaN: these bits are never set in FCLASS output
ASSUME E4M3NoInfBit ==
    \A v \in 0..255 : ~(FPClassify(v, 3) % 16 >= 8 /\ FPClassify(v, 3) % 16 < 16)

ASSUME E4M3NoSNaN ==
    \A v \in 0..255 : ~(FPClassify(v, 3) >= 32 /\ FPClassify(v, 3) < 64)

=============================================================================
