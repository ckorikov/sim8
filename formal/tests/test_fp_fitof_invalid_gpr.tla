--------------------------- MODULE test_fp_fitof_invalid_gpr ---------------------------
(*
   FITOF/FFTOI with GP register code > 3 triggers ERR_INVALID_REG.

   Valid GP registers: A=0, B=1, C=2, D=3.
   SP=4 and DP=5 are not valid targets for FITOF/FFTOI.

   Encoding: FITOF fpm, gpr  (3 bytes: op, fpm, gpr)
   FPM for FHA (fmt=1, pos=0): 1
   GPR = 4 (SP) -> FAULT(ERR_INVALID_REG)
*)

EXTENDS cpu_core

TestProgram == <<
    \* FITOF FHA, SP  (GPR=4 is invalid -> FAULT)
    OP_FITOF, 1, 4,
    OP_HLT
>>

\* Must reach FAULT with ERR_INVALID_REG
FaultIsInvalidReg == state = "FAULT" => A = ERR_INVALID_REG

=============================================================================
