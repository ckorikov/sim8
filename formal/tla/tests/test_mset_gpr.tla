---------------------------- MODULE test_mset_gpr ----------------------------
(*
   Test: MSET from GPR pair and single-register forms (opcode 189).
   MSET MA, B:A  → MA = (B<<8)|A = (2<<8)|1 = 0x0201 = 513
   MSET MB, 0x10|C  → MB = C = 7   (zero-extended single register)
*)
EXTENDS cpu_core

TestProgram == <<
    6, 0, 1,        \* MOV A, 1  (OP_MOV_RC=6: reg←constant)
    6, 1, 2,        \* MOV B, 2
    6, 2, 7,        \* MOV C, 7
    189, 0, 4,      \* MSET MA, B:A  (regH=1, regL=0 → (1<<2)|0 = 4)
    189, 1, 18,     \* MSET MB, C    (0x10|2 = 18, zero-extended C)
    0               \* HLT
>>

MustHalt  == <>(state = "HALTED")
MACorrect == state = "HALTED" => MA_reg = 513
MBCorrect == state = "HALTED" => MB_reg = 7

=============================================================================
