--------------------------- MODULE cpu_base ---------------------------
(*
   Base definitions: constants, variables, helpers
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MAX_STEPS, PROGRAM

VARIABLES
    IP, SP, DP,
    A, B, C, D,
    Z, C_flag, F,
    memory, state, step_count, cycles

vars == <<IP, SP, DP, A, B, C, D, Z, C_flag, F, memory, state, step_count, cycles>>

-----------------------------------------------------------------------------
(* Constants *)

BYTE == 0..255
STACK_MAX == 231
MEM_PAGES == 256
MEMORY_SIZE == MEM_PAGES * 256  \* 64KB full address space

REG_A == 0  REG_B == 1  REG_C == 2  REG_D == 3  REG_SP == 4  REG_DP == 5

ERR_DIV_ZERO == 1
ERR_STACK_OVERFLOW == 2
ERR_STACK_UNDERFLOW == 3
ERR_INVALID_REG == 4
ERR_PAGE_BOUNDARY == 5
ERR_INVALID_OPCODE == 6

-----------------------------------------------------------------------------
(* Opcode mnemonics *)

OP_HLT == 0
OP_MOV_RR == 1   OP_MOV_RA == 2   OP_MOV_RI == 3   OP_MOV_AR == 4
OP_MOV_IR == 5   OP_MOV_RC == 6   OP_MOV_AC == 7   OP_MOV_IC == 8
OP_ADD_RR == 10  OP_ADD_RI == 11  OP_ADD_RA == 12  OP_ADD_RC == 13
OP_SUB_RR == 14  OP_SUB_RI == 15  OP_SUB_RA == 16  OP_SUB_RC == 17
OP_INC == 18     OP_DEC == 19
OP_CMP_RR == 20  OP_CMP_RI == 21  OP_CMP_RA == 22  OP_CMP_RC == 23
OP_JMP_R == 30   OP_JMP == 31
OP_JC_R == 32    OP_JC == 33      OP_JNC_R == 34   OP_JNC == 35
OP_JZ_R == 36    OP_JZ == 37      OP_JNZ_R == 38   OP_JNZ == 39
OP_JA_R == 40    OP_JA == 41      OP_JNA_R == 42   OP_JNA == 43
OP_PUSH_R == 50  OP_PUSH_I == 51  OP_PUSH_A == 52  OP_PUSH_C == 53
OP_POP == 54
OP_CALL_R == 55  OP_CALL == 56    OP_RET == 57
OP_MUL_R == 60   OP_MUL_I == 61   OP_MUL_A == 62   OP_MUL_C == 63
OP_DIV_R == 64   OP_DIV_I == 65   OP_DIV_A == 66   OP_DIV_C == 67
OP_AND_RR == 70  OP_AND_RI == 71  OP_AND_RA == 72  OP_AND_RC == 73
OP_OR_RR == 74   OP_OR_RI == 75   OP_OR_RA == 76   OP_OR_RC == 77
OP_XOR_RR == 78  OP_XOR_RI == 79  OP_XOR_RA == 80  OP_XOR_RC == 81
OP_NOT == 82
OP_SHL_RR == 90  OP_SHL_RI == 91  OP_SHL_RA == 92  OP_SHL_RC == 93
OP_SHR_RR == 94  OP_SHR_RI == 95  OP_SHR_RA == 96  OP_SHR_RC == 97

OPCODES == {0} \cup (1..8) \cup (10..19) \cup (20..23)
           \cup (30..43) \cup (50..57) \cup (60..67)
           \cup (70..82) \cup (90..97)

-----------------------------------------------------------------------------
(* Helpers *)

RegValue(code) ==
    CASE code = 0 -> A [] code = 1 -> B [] code = 2 -> C
      [] code = 3 -> D [] code = 4 -> SP [] code = 5 -> DP [] OTHER -> 0

SetReg(code, val) ==
    CASE code = 0 -> (A' = val /\ UNCHANGED <<B,C,D,SP,DP>>)
      [] code = 1 -> (B' = val /\ UNCHANGED <<A,C,D,SP,DP>>)
      [] code = 2 -> (C' = val /\ UNCHANGED <<A,B,D,SP,DP>>)
      [] code = 3 -> (D' = val /\ UNCHANGED <<A,B,C,SP,DP>>)
      [] code = 4 -> (SP' = val /\ UNCHANGED <<A,B,C,D,DP>>)
      [] code = 5 -> (DP' = val /\ UNCHANGED <<A,B,C,D,SP>>)
      [] OTHER -> UNCHANGED <<A,B,C,D,SP,DP>>

SetRegNoSP(code, val) ==
    CASE code = 0 -> (A' = val /\ UNCHANGED <<B,C,D,SP,DP>>)
      [] code = 1 -> (B' = val /\ UNCHANGED <<A,C,D,SP,DP>>)
      [] code = 2 -> (C' = val /\ UNCHANGED <<A,B,D,SP,DP>>)
      [] code = 3 -> (D' = val /\ UNCHANGED <<A,B,C,SP,DP>>)
      [] OTHER -> UNCHANGED <<A,B,C,D,SP,DP>>

SetRegABCD(code, val) ==
    CASE code = 0 -> (A' = val /\ UNCHANGED <<B,C,D>>)
      [] code = 1 -> (B' = val /\ UNCHANGED <<A,C,D>>)
      [] code = 2 -> (C' = val /\ UNCHANGED <<A,B,D>>)
      [] code = 3 -> (D' = val /\ UNCHANGED <<A,B,C>>)
      [] OTHER -> UNCHANGED <<A,B,C,D>>

DirectAddr(addr) == (DP * 256 + addr) % MEMORY_SIZE

DecodeIndirect(encoded) ==
    LET reg == encoded % 8
        raw_off == encoded \div 8
        offset == IF raw_off > 15 THEN raw_off - 32 ELSE raw_off
        base == RegValue(reg)
        page_off == base + offset
        reg_valid == reg <= 4
        bounds_valid == (page_off >= 0) /\ (page_off <= 255)
        addr == IF reg = REG_SP THEN page_off ELSE (DP * 256 + page_off) % MEMORY_SIZE
        err == IF ~reg_valid THEN ERR_INVALID_REG
               ELSE IF ~bounds_valid THEN ERR_PAGE_BOUNDARY
               ELSE 0
    IN <<addr, err = 0, err>>

CheckOp(value) ==
    LET carry == (value >= 256) \/ (value < 0)
        wrapped == IF value >= 256 THEN value % 256
                   ELSE IF value < 0 THEN ((value % 256) + 256) % 256 ELSE value
        zero == (wrapped = 0)
    IN <<wrapped, carry, zero>>

\* Shift operations (ARM-style carry)
CheckSHL(value, cnt) ==
    LET raw == value * (2 ^ cnt)
        result == raw % 256
        carry == raw > 255
        zero == (result = 0)
    IN <<result, carry, zero>>

CheckSHR(value, cnt) ==
    LET result == value \div (2 ^ cnt)
        carry == (cnt > 0) /\ ((value % (2 ^ cnt)) # 0)
        zero == (result = 0)
    IN <<result, carry, zero>>

Mem(addr) == memory[addr % MEMORY_SIZE]

\* Bitwise operations
BitAt(n, i) == (n \div (2^i)) % 2

RECURSIVE SumBits(_, _, _, _)
SumBits(a, b, op, i) ==
    IF i > 7 THEN 0
    ELSE LET ba == BitAt(a, i)
             bb == BitAt(b, i)
             r == CASE op = "and" -> ba * bb
                    [] op = "or"  -> IF ba + bb > 0 THEN 1 ELSE 0
                    [] op = "xor" -> (ba + bb) % 2
                    [] OTHER -> 0
         IN r * (2^i) + SumBits(a, b, op, i+1)

BitAnd(a, b) == SumBits(a, b, "and", 0)
BitOr(a, b)  == SumBits(a, b, "or", 0)
BitXor(a, b) == SumBits(a, b, "xor", 0)
BitNot(a)    == 255 - a

\* Instruction size (bytes) by opcode
InstrSize(op) ==
    IF op = OP_HLT \/ op = OP_RET THEN 1
    ELSE IF op \in {OP_INC, OP_DEC, OP_NOT} \cup (30..43) \cup (50..56)
                   \cup (60..67) THEN 2
    ELSE 3  \* MOV 1-8, ADD/SUB/CMP, AND/OR/XOR, SHL/SHR

\* Instruction cost (pipeline model)
\* Stages: reg_writeback=0, simple_alu=1, mem=2, expensive_alu=2
\* Independent: max.  Dependent (data dependency): sum.
Cost(op) ==
    IF op = OP_HLT THEN 0
    ELSE IF op \in {OP_PUSH_I, OP_PUSH_A,
                    OP_MUL_I, OP_MUL_A,
                    OP_DIV_I, OP_DIV_A} THEN 4   \* mem(2)+mem(2) or mem(2)+alu(2)
    ELSE IF op \in {OP_ADD_RI, OP_ADD_RA,
                    OP_SUB_RI, OP_SUB_RA,
                    OP_CMP_RI, OP_CMP_RA,
                    OP_AND_RI, OP_AND_RA,
                    OP_OR_RI, OP_OR_RA,
                    OP_XOR_RI, OP_XOR_RA,
                    OP_SHL_RI, OP_SHL_RA,
                    OP_SHR_RI, OP_SHR_RA} THEN 3  \* mem(2)+alu(1)
    ELSE IF op \in {OP_MOV_RR, OP_MOV_RC,
                    OP_ADD_RR, OP_ADD_RC,
                    OP_SUB_RR, OP_SUB_RC,
                    OP_INC, OP_DEC,
                    OP_CMP_RR, OP_CMP_RC,
                    OP_AND_RR, OP_AND_RC,
                    OP_OR_RR, OP_OR_RC,
                    OP_XOR_RR, OP_XOR_RC,
                    OP_NOT,
                    OP_SHL_RR, OP_SHL_RC,
                    OP_SHR_RR, OP_SHR_RC}
                    \cup (30..43) THEN 1           \* alu(1) only
    ELSE 2                                         \* mem(2) only

\* Common UNCHANGED patterns
unch_jump == <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state>>
unch_cmp  == <<SP,DP,A,B,C,D,F,memory,state>>
unch_alu  == <<F,memory,state>>

\* FAULT helper
Fault(err) ==
    /\ F' = TRUE /\ A' = err /\ state' = "FAULT"
    /\ UNCHANGED <<IP, SP, DP, B, C, D, Z, C_flag, memory>>

=============================================================================
