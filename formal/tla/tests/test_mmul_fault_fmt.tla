--------------------------- MODULE test_mmul_fault_fmt ---------------------------
(*
   Test: MMUL with reserved format code 7 raises ERR_VU_FORMAT at decode.
   mfm=0x07 (bits[2:0]=7, reserved), mregs=132 (valid)
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 0, 1,   \* MSET MA, 0x0100
    188, 1, 0, 2,   \* MSET MB, 0x0200
    188, 2, 0, 3,   \* MSET MC, 0x0300
    188, 3, 2, 0,   \* MSET MM, 2
    188, 4, 2, 0,   \* MSET MN, 2
    188, 5, 2, 0,   \* MSET MK, 2
    193, 7, 132,    \* MMUL (mfm=7 = fmt=7 reserved) → ERR_VU_FORMAT
    0               \* HLT (unreachable)
>>

GotFault    == <>(state = "FAULT")
FaultIsFmt  == (state = "FAULT") => (A = ERR_VU_FORMAT)

=============================================================================
