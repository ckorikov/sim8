--------------------------- MODULE test_mmul_oob ---------------------------
(*
   Test: MMUL raises ERR_VU_OOB (surfaced via MWAIT) when A matrix exceeds 64 KB.
   MA=0xFFF1 (65521), MM=2, MK=2, fmt=F32 (sz=4)
   A extent: 65521 + 2*2*4 = 65521 + 16 = 65537 > MEM_SIZE (65536) → OOB
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 241, 255,  \* MSET MA, 0xFFF1 (65521)
    188, 1, 0, 2,      \* MSET MB, 0x0200 (512)
    188, 2, 0, 3,      \* MSET MC, 0x0300 (768)
    188, 3, 2, 0,      \* MSET MM, 2
    188, 4, 2, 0,      \* MSET MN, 2
    188, 5, 2, 0,      \* MSET MK, 2
    193, 0, 132,       \* MMUL.F.rrr MC, MA, MB
    192,               \* MWAIT — surfaces OOB fault
    0                  \* HLT (unreachable)
>>

GotFault   == <>(state = "FAULT")
FaultIsOOB == (state = "FAULT") => (A = ERR_VU_OOB)

=============================================================================
