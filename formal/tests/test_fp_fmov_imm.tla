--------------------------- MODULE test_fp_fmov_imm ---------------------------
(*
   FMOV Immediate tests: opcodes 161 (imm8) and 162 (imm16).
   161: FMOV FP, imm8 — 3 bytes [op, fpm, imm8] for OFP8 (fmt=3,4)
   162: FMOV FP, imm16 — 4 bytes [op, fpm, lo, hi] for float16/bfloat16 (fmt=1,2)

   Load imm8 into FQD (pos=3, bits [31:24]) and imm16 into FHA (pos=0, bits [15:0]).
   These sub-registers don't overlap, so both values survive to HLT.

   FPM encoding: (phys << 6) | (pos << 3) | fmt
   FQD (fmt=3, pos=3): 0*64 + 3*8 + 3 = 27
   FHA (fmt=1, pos=0): 0*64 + 0*8 + 1 = 1
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV_FI8 FQD, 0x3C (E4M3 1.5): [161, 27, 60]
    OP_FMOV_FI8, 27, 60,
    \* FMOV_FI16 FHA, 0x3E00 (float16 1.5): [162, 1, 0, 62]
    OP_FMOV_FI16, 1, 0, 62,
    OP_HLT
>>

\* FQD at fmt=3, pos=3: bits [31:24] = 60 (0x3C)
Imm8Loaded == state = "HALTED" => FPRead(0, 3, 3) = 60

\* FHA at fmt=1, pos=0: bits [15:0] = 0x3E00
Imm16Loaded == state = "HALTED" => FPRead(0, 1, 0) = 15872

\* FPSR should remain 0 (no exceptions from immediate load)
NoFPSRChange == state = "HALTED" => FPSR_reg = 0

=============================================================================
