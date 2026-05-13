--------------------------- MODULE test_mmul ---------------------------
(*
   Test: MMUL.F auto-increments MA and MB at enqueue time.
   MC is intentionally NOT auto-incremented.
   MA=0x0100, MB=0x0200, MC=0x0300, MM=4, MN=4, MK=4, fmt=F32 (sz=4)
   Expected: MA += M*K*4=64, MB += K*N*4=64, MC unchanged.
   mfm=0x00 (fmt=0=F32, layout=.rrr), mregs=(MC<<6)|(MA<<4)|(MB<<2)=128|0|4=132
*)
EXTENDS cpu_core

TestProgram == <<
    188, 0, 0, 1,    \* MSET MA, 0x0100 (256)
    188, 1, 0, 2,    \* MSET MB, 0x0200 (512)
    188, 2, 0, 3,    \* MSET MC, 0x0300 (768)
    188, 3, 4, 0,    \* MSET MM, 4
    188, 4, 4, 0,    \* MSET MN, 4
    188, 5, 4, 0,    \* MSET MK, 4
    193, 0, 132,     \* MMUL.F.rrr MC, MA, MB
    192,             \* MWAIT
    0                \* HLT
>>

MAIncr  == (state = "HALTED") => (MA_reg = 256 + 64)
MBIncr  == (state = "HALTED") => (MB_reg = 512 + 64)
MCIncr  == (state = "HALTED") => (MC_reg = 768)
NoFault == (state = "HALTED") => ~F

MustTerminate == <>(state = "HALTED")

=============================================================================
