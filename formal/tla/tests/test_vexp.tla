--------------------------- MODULE test_vexp ---------------------------
(*
   Test: VEXP.F.vv — element-wise exp issue + auto-increment.

   Verifies: queue push (no decode fault) and that VEXP is unary —
   only VA (src1) and VC (dst) advance; VB is untouched.
*)

EXTENDS cpu_core

TestProgram == <<
    \* VSET VA, #0x0100  — src1 base
    OP_VSET_IMM16, 0, 0, 1,
    \* VSET VB, #0x0200  — sentinel (must NOT advance for unary)
    OP_VSET_IMM16, 1, 0, 2,
    \* VSET VC, #0x0120  — dst
    OP_VSET_IMM16, 2, 32, 1,
    \* VSET VL, #4
    OP_VSET_IMM16, 4, 4, 0,
    \* VEXP.F VC, VA
    \* opcode=187, vfm=(0<<3)|0=0 (F32, vv-unary), regs=(2<<6)|(0<<4)=128
    187, 0, 128,
    \* VWAIT
    OP_VWAIT,
    OP_HLT
>>

\* Auto-increment: VA += 16, VC += 16, VB unchanged
VAIncr  == (state = "HALTED") => (VA_reg = 256 + 16)
VBNoInc == (state = "HALTED") => (VB_reg = 512)
VCIncr  == (state = "HALTED") => (VC_reg = 288 + 16)

NoFault == (state = "HALTED") => ~F

MustTerminate == <>(state = "HALTED")

=============================================================================
