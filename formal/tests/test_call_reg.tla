--------------------------- MODULE test_call_reg ---------------------------
(*
   CALL reg (opcode 55): jump to address in register, push return address.
*)

EXTENDS cpu_core

TestProgram == <<
    OP_MOV_RC, REG_B, 10,        \* bytes 0-2: B = 10
    OP_CALL_R, REG_B,            \* bytes 3-4: push IP+2=5, jump to B=10
    OP_MOV_RC, REG_A, 99,        \* bytes 5-7: A = 99 (return lands here)
    OP_HLT,                      \* byte 8
    0,                           \* byte 9: padding
    OP_MOV_RC, REG_C, 77,        \* bytes 10-12: C = 77 (subroutine)
    OP_RET                       \* byte 13: pop 5, jump to addr 5
>>

\* Subroutine sets C = 77, return path sets A = 99
CallRegWorks == (state = "HALTED") => (C = 77 /\ A = 99)

=============================================================================
