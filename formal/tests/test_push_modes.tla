--------------------------- MODULE test_push_modes ---------------------------
(*
   PUSH with indirect and direct address modes: PUSH [reg] (51), PUSH [addr] (52)
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_AC, 100, 77,          \* mem[100] = 77
    OP_MOV_RC, REG_B, 100,       \* B = 100
    OP_PUSH_I, 1,                \* PUSH [B+0]: push mem[100] = 77, SP = 230
    OP_PUSH_A, 100,              \* PUSH [100]: push mem[100] = 77, SP = 229
    OP_POP, REG_A,               \* A = 77, SP = 230
    OP_POP, REG_C,               \* C = 77, SP = 231 = STACK_MAX
    OP_HLT
>>

\* Both pushes stored 77; both pops should retrieve 77; SP restored
PushIndirectCorrect == (state = "HALTED") => (A = 77 /\ C = 77 /\ SP = STACK_MAX)

=============================================================================
