--------------------------- MODULE cpu_ops_stack ---------------------------
(* Stack operations: PUSH 50-53, POP 54, CALL 55-56, RET 57 *)
EXTENDS cpu_base

\* PUSH (50-53) - check SP BEFORE memory write
ExecPUSH_50 == memory[IP] = OP_PUSH_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF SP = 0 THEN Fault(ERR_STACK_OVERFLOW)
       ELSE memory' = [memory EXCEPT ![SP] = RegValue(reg)]
            /\ SP' = SP - 1 /\ IP' = IP + 2
            /\ UNCHANGED <<DP,A,B,C,D,F,state,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

ExecPUSH_51 == memory[IP] = OP_PUSH_I
    /\ LET dec == DecodeIndirect(Mem(IP+1)) IN
       IF ~dec[2] THEN Fault(dec[3])
       ELSE IF SP = 0 THEN Fault(ERR_STACK_OVERFLOW)
       ELSE memory' = [memory EXCEPT ![SP] = Mem(dec[1])]
            /\ SP' = SP - 1 /\ IP' = IP + 2
            /\ UNCHANGED <<DP,A,B,C,D,F,state,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

ExecPUSH_52 == memory[IP] = OP_PUSH_A
    /\ LET a == DirectAddr(Mem(IP+1)) IN
       IF SP = 0 THEN Fault(ERR_STACK_OVERFLOW)
       ELSE memory' = [memory EXCEPT ![SP] = Mem(a)]
            /\ SP' = SP - 1 /\ IP' = IP + 2
            /\ UNCHANGED <<DP,A,B,C,D,F,state,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

ExecPUSH_53 == memory[IP] = OP_PUSH_C
    /\ IF SP = 0 THEN Fault(ERR_STACK_OVERFLOW)
       ELSE memory' = [memory EXCEPT ![SP] = Mem(IP+1)]
            /\ SP' = SP - 1 /\ IP' = IP + 2
            /\ UNCHANGED <<DP,A,B,C,D,F,state,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

\* POP (54) - check SP before read
ExecPOP_54 == memory[IP] = OP_POP
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF SP >= STACK_MAX THEN Fault(ERR_STACK_UNDERFLOW)
       ELSE LET v == memory[SP+1] IN
            SetRegABCD(reg, v)
            /\ SP' = SP + 1 /\ IP' = IP + 2
            /\ UNCHANGED <<DP,F,state,memory,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

\* CALL (55-56) - check SP BEFORE memory write
ExecCALL_55 == memory[IP] = OP_CALL_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF SP = 0 THEN Fault(ERR_STACK_OVERFLOW)
       ELSE memory' = [memory EXCEPT ![SP] = (IP + 2) % 256]
            /\ SP' = SP - 1 /\ IP' = RegValue(reg)
            /\ UNCHANGED <<DP,A,B,C,D,F,state,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

ExecCALL_56 == memory[IP] = OP_CALL
    /\ IF SP = 0 THEN Fault(ERR_STACK_OVERFLOW)
       ELSE memory' = [memory EXCEPT ![SP] = (IP + 2) % 256]
            /\ SP' = SP - 1 /\ IP' = Mem(IP+1)
            /\ UNCHANGED <<DP,A,B,C,D,F,state,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

\* RET (57) - check SP before read
ExecRET_57 == memory[IP] = OP_RET
    /\ IF SP >= STACK_MAX THEN Fault(ERR_STACK_UNDERFLOW)
       ELSE SP' = SP + 1 /\ IP' = memory[SP+1]
            /\ UNCHANGED <<DP,A,B,C,D,F,state,memory,Z,C_flag,FA_reg,FPCR_reg,FPSR_reg>>

=============================================================================
