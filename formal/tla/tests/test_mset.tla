--------------------------- MODULE test_mset ---------------------------
(*
   Test: MSET_IMM16 sets all six MU registers correctly.
   MA=0x0100, MB=0x0200, MC=0x0300, MM=4, MN=4, MK=4
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 0, 1,    \* MSET MA, 0x0100
    188, 1, 0, 2,    \* MSET MB, 0x0200
    188, 2, 0, 3,    \* MSET MC, 0x0300
    188, 3, 4, 0,    \* MSET MM, 4
    188, 4, 4, 0,    \* MSET MN, 4
    188, 5, 4, 0,    \* MSET MK, 4
    0                \* HLT
>>

MASet   == (state = "HALTED") => (MA_reg = 256)
MBSet   == (state = "HALTED") => (MB_reg = 512)
MCSet   == (state = "HALTED") => (MC_reg = 768)
MMSet   == (state = "HALTED") => (MM_reg = 4)
MNSet   == (state = "HALTED") => (MN_reg = 4)
MKSet   == (state = "HALTED") => (MK_reg = 4)
NoFault == (state = "HALTED") => ~F

MustTerminate == <>(state = "HALTED")

=============================================================================
