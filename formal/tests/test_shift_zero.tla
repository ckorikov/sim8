--------------------------- MODULE test_shift_zero ---------------------------
(*
   Test: SHL/SHR by 0 must preserve C flag (spec: "Shift by 0: C is unchanged")
*)

EXTENDS cpu_core

TestProgram == <<
    \* Set C=TRUE via overflow: ADD 200+100=300 > 255 → C=TRUE
    OP_MOV_RC, REG_A, 200,
    OP_ADD_RC, REG_A, 100,     \* A = 44 (300%256), C = TRUE

    \* SHL A, 0 -- must keep C=TRUE
    OP_MOV_RC, REG_B, 0,       \* B = 0
    OP_SHL_RR, REG_A, REG_B,   \* shift by 0: A unchanged, C must stay TRUE

    \* Save A to C reg for later check
    OP_MOV_RR, REG_C, REG_A,

    \* Now test SHR by 0 with immediate form
    \* First set C=TRUE again: SUB 0-1 → C=TRUE (borrow)
    OP_MOV_RC, REG_A, 0,
    OP_SUB_RC, REG_A, 1,       \* A = 255, C = TRUE

    \* SHR A, 0 -- must keep C=TRUE
    OP_SHR_RC, REG_A, 0,       \* shift by 0: A unchanged, C must stay TRUE

    OP_HLT
>>

\* After SHL by 0 (IP past SHL_RR at byte 12, before next MOV_RR at 15):
\* C_flag must still be TRUE
SHLZeroPreservesC == (IP = 15) => (C_flag = TRUE /\ A = 44)

\* At halt: C_flag must be TRUE (SHR by 0 preserved it)
SHRZeroPreservesC == (state = "HALTED") => (C_flag = TRUE /\ A = 255)

=============================================================================
