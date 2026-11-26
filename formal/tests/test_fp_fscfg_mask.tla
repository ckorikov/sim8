--------------------------- MODULE test_fp_fscfg_mask ---------------------------
(*
   FSCFG masks reserved bits: writing 0xFF to FPCR stores only bits [1:0].

   FPCR holds only the rounding mode (2 bits). Bits [7:2] are reserved and
   masked to 0 on write (impl: val % 4).
   Writing 255 (0xFF) should result in FPCR=3 and FCFG reading back 3.

   Per spec/fp.md FSCFG: "Only bits [1:0] (RM) are writable; upper bits masked."
*)

EXTENDS cpu_core

TestProgram == <<
    \* MOV A, 255
    OP_MOV_RC, REG_A, 255,
    \* FSCFG A -- write A(=255) to FPCR; should store 255 % 4 = 3
    OP_FSCFG, REG_A,
    \* FCFG B -- read FPCR -> B
    OP_FCFG, REG_B,
    OP_HLT
>>

\* FPCR holds only the 2 RM bits: 255 % 4 = 3
FSCFGMasksReserved == state = "HALTED" => (FPCR_reg = 3 /\ B = 3)

=============================================================================
