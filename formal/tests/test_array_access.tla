------------------------- MODULE test_array_access -------------------------
(*
   Array access: read contiguous bytes via indirect addressing with
   incrementing index. Verifies that memory[base + i] returns correct
   values for each element of an inline data array.

   Layout:
     addr 0..14: code (JMP over data, then read loop)
     addr 15..19: data array = <<10, 20, 30, 40, 50>>
*)

EXTENDS cpu_core

\* Array data lives at address 15, length 5
ArrayBase == 15
ArrayLen  == 5

TestProgram == <<
    \* 0: JMP past array data to code start
    OP_JMP, 20,

    \* 2..14: padding (zeros) to reach addr 15
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,

    \* 15..19: array data (equivalent to DB 10, 20, 30, 40, 50)
    10, 20, 30, 40, 50,

    \* 20: MOV B, ArrayBase  (B = index register, starts at base)
    OP_MOV_RC, REG_B, ArrayBase,

    \* 23: MOV A, [B+0]   -- read array[0] = 10
    OP_MOV_RI, REG_A, 1,       \* regaddr = (0<<3)|1 = 1  => mem[B+0]

    \* 26: MOV C, A        -- save array[0] to C
    OP_MOV_RR, REG_C, REG_A,

    \* 29: INC B           -- B = 16
    OP_INC, REG_B,

    \* 31: MOV A, [B+0]   -- read array[1] = 20
    OP_MOV_RI, REG_A, 1,

    \* 34: MOV D, A        -- save array[1] to D
    OP_MOV_RR, REG_D, REG_A,

    \* 37: INC B           -- B = 17
    OP_INC, REG_B,

    \* 39: MOV A, [B+0]   -- read array[2] = 30, keep in A
    OP_MOV_RI, REG_A, 1,

    \* 42: HLT
    OP_HLT
>>

\* After halt: C = array[0], D = array[1], A = array[2]
ArrayElement0 == (state = "HALTED") => (C = 10)
ArrayElement1 == (state = "HALTED") => (D = 20)
ArrayElement2 == (state = "HALTED") => (A = 30)

\* Index register points past last read element
IndexAdvanced == (state = "HALTED") => (B = ArrayBase + 2)

=============================================================================
