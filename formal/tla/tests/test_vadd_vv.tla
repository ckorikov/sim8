--------------------------- MODULE test_vadd_vv ---------------------------
(*
   Test: VADD.I.vv — INT8 vector-vector add
   Verifies: queue push, VU execution, auto-increment, memory write

   Uses MOV + DP to place test data at 0x0100 and 0x0110.
   Result at 0x0120. VL=4, INT8.
*)

EXTENDS cpu_core

TestProgram == <<
    \* Set DP=1 to write to page 1 (0x0100+)
    OP_MOV_RC, REG_DP, 1,
    \* Write src1: [10, 20, 30, 40] at page1:0x00..0x03 = 0x0100..0x0103
    OP_MOV_AC, 0, 10,
    OP_MOV_AC, 1, 20,
    OP_MOV_AC, 2, 30,
    OP_MOV_AC, 3, 40,
    \* Write src2: [1, 2, 3, 4] at page1:0x10..0x13 = 0x0110..0x0113
    OP_MOV_AC, 16, 1,
    OP_MOV_AC, 17, 2,
    OP_MOV_AC, 18, 3,
    OP_MOV_AC, 19, 4,
    \* Reset DP
    OP_MOV_RC, REG_DP, 0,
    \* VSET VA, #0x0100
    OP_VSET_IMM16, 0, 0, 1,
    \* VSET VB, #0x0110
    OP_VSET_IMM16, 1, 16, 1,
    \* VSET VC, #0x0120
    OP_VSET_IMM16, 2, 32, 1,
    \* VSET VL, #4 (imm16: lo=4, hi=0)
    OP_VSET_IMM16, 4, 4, 0,
    \* VADD.I.vv VC, VA, VB
    \* opcode=170, vfm=(0<<5)|(0<<3)|5=5 (INT8, vv), regs=(2<<6)|(0<<4)|(1<<2)=132
    170, 5, 132,
    \* VWAIT
    OP_VWAIT,
    OP_HLT
>>

\* Auto-increment: VA += 4, VB += 4, VC += 4
VAIncr == (state = "HALTED") => (VA_reg = 260)
VBIncr == (state = "HALTED") => (VB_reg = 276)
VCIncr == (state = "HALTED") => (VC_reg = 292)

\* Result: dst[i] = src1[i] + src2[i]
Result0 == (state = "HALTED") => (memory[288] = 11)
Result1 == (state = "HALTED") => (memory[289] = 22)
Result2 == (state = "HALTED") => (memory[290] = 33)
Result3 == (state = "HALTED") => (memory[291] = 44)

MustTerminate == <>(state = "HALTED")

=============================================================================
