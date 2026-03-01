--------------------------- MODULE test_fp_fb_min ---------------------------
(*
   FB register test: verify that phys=1 writes to FB_reg, not FA_reg.
   Uses float16 format (fmt=1).

   FPM encoding: phys*64 + pos*8 + fmt
   phys=0, pos=0, fmt=1 => FPM = 0*64 + 0*8 + 1 = 1   (FA, FHA)
   phys=1, pos=0, fmt=1 => FPM = 1*64 + 0*8 + 1 = 65   (FB, FHA)

   Test program:
   1. FMOV FP(FA,FHA), [240]  -- load 0 into FA (phys=0, FPM=1)
   2. FMOV FP(FB,FHA), imm16 0x3C00 (1.0 in float16) -- load 1.0 into FB (phys=1, FPM=65)
   3. FABS FP(FB,FHA) -- abs of 1.0 in FB (phys=1, FPM=65)
   4. FNEG FP(FB,FHA) -- neg of 1.0 in FB -> -1.0 (phys=1, FPM=65)
   5. HLT

   Expected: FA_reg = 0, FB_reg has -1.0 in float16 = 0xBC00 = 48128
*)

EXTENDS cpu_core

TestProgram == <<
    \* FMOV FA.FHA, [240] -- load +0.0 from zero memory (FPM=1, phys=0)
    OP_FMOV_FA, 1, 240,
    \* FMOV FB.FHA, imm16 0x3C00 (15360 = 1.0 in float16) (FPM=65, phys=1)
    OP_FMOV_FI16, 65, 0, 60,
    \* FABS FB.FHA (FPM=65, phys=1) -- abs(1.0) = 1.0
    OP_FABS, 65,
    \* FNEG FB.FHA (FPM=65, phys=1) -- neg(1.0) = -1.0 = 0xBC00 = 48128
    OP_FNEG, 65,
    OP_HLT
>>

\* FA_reg unchanged (stays 0) after FB operations
FAUnchanged == state = "HALTED" => FA_reg = 0

\* FB_reg should contain -1.0 in float16 (0xBC00 = 48128)
FBHasNeg1 == state = "HALTED" => FB_reg = 48128

\* Both registers non-negative
FANonNeg == FA_reg >= 0
FBNonNeg == FB_reg >= 0

=============================================================================
