--------------------------- MODULE test_vset ---------------------------
(*
   Test: VSET immediate, GPR pair, VL; verify register values after HLT
*)

EXTENDS cpu_core

TestProgram == <<
    \* VSET VA, #0x0200 (opcode 163, target=0, lo=0x00, hi=0x02)
    OP_VSET_IMM16, 0, 0, 2,
    \* VSET VB, #0x0300
    OP_VSET_IMM16, 1, 0, 3,
    \* VSET VC, #0x0400
    OP_VSET_IMM16, 2, 0, 4,
    \* VSET VM, #0x0500
    OP_VSET_IMM16, 3, 0, 5,
    \* VSET VL, #8 (imm16: lo=8, hi=0)
    OP_VSET_IMM16, 4, 8, 0,
    \* MOV A, 1 (for GPR pair test)
    OP_MOV_RC, REG_A, 1,
    \* MOV B, 0x50
    OP_MOV_RC, REG_B, 80,
    \* VSET VA, A, B (opcode 164, target=0, packed=(0<<2)|1 = 1)
    OP_VSET_GPR, 0, 1,
    OP_HLT
>>

\* After execution:
\* VA = A:B = 0x0150 (A=1, B=80=0x50)
\* VB = 0x0300
\* VC = 0x0400
\* VM = 0x0500
\* VL = 8
VACorrect == (state = "HALTED") => (VA_reg = 336)     \* 0x0150 = 336
VBCorrect == (state = "HALTED") => (VB_reg = 768)     \* 0x0300
VCCorrect == (state = "HALTED") => (VC_reg = 1024)    \* 0x0400
VMCorrect == (state = "HALTED") => (VM_reg = 1280)    \* 0x0500
VLCorrect == (state = "HALTED") => (VL_reg = 8)

=============================================================================
