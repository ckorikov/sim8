--------------------------- MODULE test_fp_load_store ---------------------------
(*
   FP load/store: FMOV with float16 (2 bytes).
   Load +0.0 from zero-init memory, store to mem[240..241], load back.
   float16 at addr 240: 240+2-1=241 <= 255, within page.
   FPM=1 means fmt=1 (float16), pos=0, phys=0.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_FMOV_FA, 1, 240,
    OP_FMOV_AF, 1, 240,
    OP_FMOV_FA, 1, 240,
    OP_HLT
>>

=============================================================================
