--------------------------- MODULE test_fp_cost ---------------------------
(*
   Verify the FP pipeline cost model against the cycle counter.

   Instruction sequence (FP16 throughout, FPM_FHA=1, FPM_FHB=9):
     1. FDIV_RR  FHA, FHB        cost = fpu_d(3)             -> cycles =  3
     2. FMOV_FA  FHA, [240]      cost = mem(FP16)=2          -> cycles =  5
     3. FMADD_A  FHA, FHB, [240] cost = mem(FP16)+fpu_ma(4)=6 -> cycles = 11
     4. FDIV_A   FHA, [240]      cost = mem(FP16)+fpu_d(3)=5 -> cycles = 16
     5. HLT                      cost = 0                    -> cycles = 16

   FPM encoding: (phys << 6) | (pos << 3) | fmt
   FHA: fmt=1, pos=0, phys=0 -> FPM=1
   FHB: fmt=1, pos=1, phys=0 -> FPM=9
*)

EXTENDS cpu_core

TestProgram == <<
    \* 1. FDIV_RR FHA, FHB  [3 bytes]
    OP_FDIV_RR, 1, 9,
    \* 2. FMOV_FA FHA, [240] [3 bytes]
    OP_FMOV_FA, 1, 240,
    \* 3. FMADD_A FHA, FHB, [240] [4 bytes]
    OP_FMADD_A, 1, 9, 240,
    \* 4. FDIV_A FHA, [240] [3 bytes]
    OP_FDIV_A, 1, 240,
    \* 5. HLT
    OP_HLT
>>

\* After HALTED, cycle counter must equal exactly 16
CostModelCorrect == state = "HALTED" => cycles = 16

=============================================================================
