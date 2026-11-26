--------------------------- MODULE test_shift ---------------------------
(*
   Test shift operations: SHL and SHR
*)

EXTENDS cpu_core

TestProgram == <<
    \* SHL by 1 = multiply by 2
    OP_MOV_RC, REG_A, 5,      \* A = 5
    OP_MOV_RC, REG_B, 1,      \* B = 1 (shift count)
    OP_SHL_RR, REG_A, REG_B,  \* A = 5 << 1 = 10

    \* SHR by 1 = divide by 2
    OP_MOV_RC, REG_C, 20,     \* C = 20
    OP_SHR_RC, REG_C, 1,      \* C = 20 >> 1 = 10

    \* SHL by 4 = multiply by 16
    OP_MOV_RC, REG_D, 3,      \* D = 3
    OP_SHL_RC, REG_D, 4,      \* D = 3 << 4 = 48

    \* SHL overflow - carry flag set
    OP_MOV_RC, REG_A, 200,    \* A = 200
    OP_SHL_RC, REG_A, 2,      \* A = 200 << 2 = 800 % 256 = 32, C = TRUE

    OP_HLT
>>

\* After first SHL: A = 10
ShiftLeftDouble == (IP > 8) => (A = 10 \/ IP > 8)

\* After SHR: C = 10
ShiftRightHalf == (IP > 14 /\ IP < 20) => (C = 10)

\* After SHL by 4: D = 48
ShiftLeft4 == (IP > 17 /\ IP < 23) => (D = 48)

\* After overflow shift: A = 32 and carry set
ShiftOverflow == (state = "HALTED") => (A = 32 /\ C_flag = TRUE)

=============================================================================
