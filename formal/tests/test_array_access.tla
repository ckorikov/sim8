------------------------- MODULE test_array_access -------------------------
(*
   Array access via indirect addressing with incrementing index.
   Data bytes are placed right after JMP, read back with MOV reg, [B+0].
*)

EXTENDS cpu_core

ArrayBase == 2  \* array starts at addr 2 (right after JMP instruction)
ArrayLen  == 5

TestProgram == <<
    OP_JMP, 7,              \* skip over data

    10, 20, 30, 40, 50,     \* array at addr 2..6

    OP_MOV_RC, REG_B, ArrayBase,
    OP_MOV_RI, REG_A, 1,    \* A = mem[B+0] = array[0], regaddr=(0<<3)|1
    OP_MOV_RR, REG_C, REG_A,
    OP_INC, REG_B,
    OP_MOV_RI, REG_A, 1,    \* A = array[1]
    OP_MOV_RR, REG_D, REG_A,
    OP_INC, REG_B,
    OP_MOV_RI, REG_A, 1,    \* A = array[2]
    OP_HLT
>>

\* C = array[0], D = array[1], A = array[2]
ArrayElement0 == (state = "HALTED") => (C = 10)
ArrayElement1 == (state = "HALTED") => (D = 20)
ArrayElement2 == (state = "HALTED") => (A = 30)

IndexAdvanced == (state = "HALTED") => (B = ArrayBase + 2)

\* Data region is never modified (read-only access has no side effects)
DataIntact == \A i \in ArrayBase..(ArrayBase + ArrayLen - 1) : memory[i] = InitMem[i]

=============================================================================
