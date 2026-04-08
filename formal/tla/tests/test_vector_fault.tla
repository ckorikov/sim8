--------------------------- MODULE test_vector_fault ---------------------------
(*
   Test: VU fault conditions
   1. VDOT.I triggers ERR_VU_FORMAT (INT8 dot not supported)
   2. Invalid fmt code (7) triggers ERR_VU_FORMAT
   3. Invalid VSET target triggers ERR_INVALID_REG
*)

EXTENDS cpu_core

\* Test 1: VDOT.I — fmt=5(INT8) with VDOT should FAULT
TestProgram == <<
    \* VSET VL, #4 (imm16: lo=4, hi=0)
    OP_VSET_IMM16, 4, 4, 0,
    \* VSET VA, #0x0100
    OP_VSET_IMM16, 0, 0, 1,
    \* VSET VB, #0x0110
    OP_VSET_IMM16, 1, 16, 1,
    \* VSET VC, #0x0120
    OP_VSET_IMM16, 2, 32, 1,
    \* VDOT.I — opcode=176, vfm = (0<<5)|(0<<3)|5 = 5, regs = (2<<6)|(0<<4)|(1<<2) = 132
    176, 5, 132,
    OP_HLT
>>

\* VDOT.I should cause FAULT with ERR_VU_FORMAT
MustFault == <>(state = "FAULT")
FaultCode == (state = "FAULT") => (A = ERR_VU_FORMAT)

=============================================================================
