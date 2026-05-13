--------------------------- MODULE test_vfmadd ---------------------------
(*
   Test: VFMADD.F.vv — fused multiply-add issue + auto-increment.

   Verifies: queue push (no decode fault), auto-increment of VA, VB, VC by S
   (full vector). Uses nondeterministic FP oracle for result values; this test
   only checks issuance and pointer updates, mirroring test_vadd_vv.
*)

EXTENDS cpu_core

TestProgram == <<
    \* VSET VA, #0x0100  — src1 base
    OP_VSET_IMM16, 0, 0, 1,
    \* VSET VB, #0x0110  — src2 base
    OP_VSET_IMM16, 1, 16, 1,
    \* VSET VC, #0x0120  — dst (read-modify-write)
    OP_VSET_IMM16, 2, 32, 1,
    \* VSET VL, #4
    OP_VSET_IMM16, 4, 4, 0,
    \* VFMADD.F.vv VC, VA, VB
    \* opcode=186, vfm=(0<<3)|0=0 (F32, vv), regs=(2<<6)|(0<<4)|(1<<2)=132
    186, 0, 132,
    \* VWAIT
    OP_VWAIT,
    OP_HLT
>>

\* Auto-increment: VA += 16 (4 elems × 4 bytes), VB += 16, VC += 16
VAIncr == (state = "HALTED") => (VA_reg = 256 + 16)
VBIncr == (state = "HALTED") => (VB_reg = 272 + 16)
VCIncr == (state = "HALTED") => (VC_reg = 288 + 16)

\* No fault expected
NoFault == (state = "HALTED") => ~F

MustTerminate == <>(state = "HALTED")

=============================================================================
