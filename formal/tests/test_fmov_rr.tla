--------------------------- MODULE test_fmov_rr ---------------------------
(*
   FMOV_RR: register-to-register copy within the same format.

   FPM for FHA (fmt=1, pos=0): 1
   FPM for FHB (fmt=1, pos=1): 9
   FMOV_RR FHA, FHB copies FHB half-slot into FHA half-slot.
   Same fmt=1 -> valid, should HALT.
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV_RR FHA, FHB  (same fmt=1, different pos -> valid copy)
    OP_FMOV_RR, 1, 9,
    OP_HLT
>>

\* Must reach HALTED (not fault on same-format copy)
ReachesHalted == <>(state = "HALTED")

\* FA_reg must remain non-negative (sanity)
FANonNeg == FA_reg >= 0

=============================================================================
