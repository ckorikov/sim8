----------------------- MODULE test_mmul_fault_mfm_rsvd -----------------------
(*
   Test: MMUL with mfm bits[7:6] != 0 → ERR_VU_FORMAT.
   mfm = 0xC0 = 192 → bits[7:6] = 3 (non-zero reserved) → invalid.
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 0, 1,   \* MSET MA, 0x0100
    188, 1, 0, 2,   \* MSET MB, 0x0200
    188, 2, 0, 3,   \* MSET MC, 0x0300
    188, 3, 2, 0,   \* MSET MM, 2
    188, 4, 2, 0,   \* MSET MN, 2
    188, 5, 2, 0,   \* MSET MK, 2
    193, 192, 8,    \* MMUL mfm=0xC0 (bits[7:6]=3 reserved) → ERR_VU_FORMAT
    0               \* HLT (unreachable)
>>

GotFault   == <>(state = "FAULT")
FaultIsFmt == (state = "FAULT") => (A = ERR_VU_FORMAT)

=============================================================================
