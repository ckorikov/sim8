--------------------------- MODULE test_mmad ---------------------------
(*
   Test: MMAD.H auto-increments MA / MB only (FP16, sz=2).
   MC is intentionally NOT auto-incremented so K-loop accumulation stays cheap.
   MA=0x0100, MB=0x0200, MC=0x0300, MM=4, MN=4, MK=4, fmt=F16 (sz=2)
   Expected:
     MA += M*K*sz = 4*4*2 = 32   (A-role stride)
     MB += K*N*sz = 4*4*2 = 32   (B-role stride)
     MC unchanged
   mfm=0x01 (fmt=1=F16, layout=.rrr), mregs=132
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 0, 1,    \* MSET MA, 0x0100 (256)
    188, 1, 0, 2,    \* MSET MB, 0x0200 (512)
    188, 2, 0, 3,    \* MSET MC, 0x0300 (768)
    188, 3, 4, 0,    \* MSET MM, 4
    188, 4, 4, 0,    \* MSET MN, 4
    188, 5, 4, 0,    \* MSET MK, 4
    194, 1, 132,     \* MMAD.H.rrr MC, MA, MB
    192,             \* MWAIT
    0                \* HLT
>>

MAIncr  == (state = "HALTED") => (MA_reg = 256 + 32)
MBIncr  == (state = "HALTED") => (MB_reg = 512 + 32)
MCIncr  == (state = "HALTED") => (MC_reg = 768)
NoFault == (state = "HALTED") => ~F

MustTerminate == <>(state = "HALTED")

=============================================================================
