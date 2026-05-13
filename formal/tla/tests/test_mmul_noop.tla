--------------------------- MODULE test_mmul_noop ---------------------------
(*
   Test: MMUL with MM=0 is a no-op — MA/MB/MC not incremented.
   Spec: "M=0 or N=0 or K=0 makes the command a no-op"
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 0, 1,   \* MSET MA, 0x0100 (256)
    188, 1, 0, 2,   \* MSET MB, 0x0200 (512)
    188, 2, 0, 3,   \* MSET MC, 0x0300 (768)
    188, 3, 0, 0,   \* MSET MM, 0  ← zero dimension
    188, 4, 4, 0,   \* MSET MN, 4
    188, 5, 4, 0,   \* MSET MK, 4
    193, 0, 132,    \* MMUL.F.rrr MC, MA, MB  → no-op
    192,            \* MWAIT (queue empty, no fault)
    0               \* HLT
>>

MANoInc == (state = "HALTED") => (MA_reg = 256)
MBNoInc == (state = "HALTED") => (MB_reg = 512)
MCNoInc == (state = "HALTED") => (MC_reg = 768)
NoFault == (state = "HALTED") => ~F

MustTerminate == <>(state = "HALTED")

=============================================================================
