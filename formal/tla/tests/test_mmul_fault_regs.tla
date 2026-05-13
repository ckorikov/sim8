--------------------------- MODULE test_mmul_fault_regs ---------------------------
(*
   Test: MMUL with mregs operand code > 2 (MM register as src2) → ERR_VU_FORMAT.
   mregs = (MC<<6)|(MA<<4)|(MM<<2) = (2<<6)|(0<<4)|(3<<2) = 128|0|12 = 140 = 0x8C
   src2=3 → register code > 2 → invalid (only MA/MB/MC valid as pointer operands)
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 0, 1,   \* MSET MA, 0x0100
    188, 1, 0, 2,   \* MSET MB, 0x0200
    188, 2, 0, 3,   \* MSET MC, 0x0300
    188, 3, 2, 0,   \* MSET MM, 2
    188, 4, 2, 0,   \* MSET MN, 2
    188, 5, 2, 0,   \* MSET MK, 2
    193, 0, 140,    \* MMUL.F (mfm=0, mregs=0x8C: src2=3=MM → invalid) → ERR_VU_FORMAT
    0               \* HLT (unreachable)
>>

GotFault   == <>(state = "FAULT")
FaultIsFmt == (state = "FAULT") => (A = ERR_VU_FORMAT)

=============================================================================
