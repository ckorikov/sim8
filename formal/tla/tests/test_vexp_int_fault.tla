--------------------------- MODULE test_vexp_int_fault ---------------------------
(*
   Test: VEXP.U → FAULT(ERR_VU_FORMAT).

   VEXP is FP-only; integer formats (.U=5, .I=6) must fault at decode time.
*)

EXTENDS cpu_core

TestProgram == <<
    \* VSET VL, #4
    OP_VSET_IMM16, 4, 4, 0,
    \* VEXP.U VC, VA  — fmt=5 (U), should fault
    \* opcode=187, vfm=(0<<3)|5=5, regs=(2<<6)|(0<<4)=128
    187, 5, 128,
    OP_HLT
>>

\* Should fault with ERR_VU_FORMAT
DidFault == <>(state = "FAULT" /\ A = ERR_VU_FORMAT)

=============================================================================
