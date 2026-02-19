--------------------------- MODULE cpu_ops_mul ---------------------------
(* Multiplication and Division: MUL 60-63, DIV 64-67 *)
EXTENDS cpu_base

\* MUL (60-63) - result in A, uses CheckOp for overflow
ExecMUL_60 == memory[IP] = OP_MUL_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(A * RegValue(reg)) IN
            A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
            /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMUL_61 == memory[IP] = OP_MUL_I
    /\ LET dec == DecodeIndirect(Mem(IP+1)) IN
       IF ~dec[2] THEN Fault(dec[3])
       ELSE LET r == CheckOp(A * Mem(dec[1])) IN
            A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
            /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMUL_62 == memory[IP] = OP_MUL_A
    /\ LET a == DirectAddr(Mem(IP+1)) r == CheckOp(A * Mem(a)) IN
       A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
       /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMUL_63 == memory[IP] = OP_MUL_C
    /\ LET v == Mem(IP+1) r == CheckOp(A * v) IN
       A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
       /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

\* DIV (64-67) - division by zero causes fault
ExecDIV_64 == memory[IP] = OP_DIV_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET v == RegValue(reg) IN
            IF v = 0 THEN Fault(ERR_DIV_ZERO)
            ELSE LET r == CheckOp(A \div v) IN
                 A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
                 /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecDIV_65 == memory[IP] = OP_DIV_I
    /\ LET dec == DecodeIndirect(Mem(IP+1)) IN
       IF ~dec[2] THEN Fault(dec[3])
       ELSE LET v == Mem(dec[1]) IN
            IF v = 0 THEN Fault(ERR_DIV_ZERO)
            ELSE LET r == CheckOp(A \div v) IN
                 A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
                 /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecDIV_66 == memory[IP] = OP_DIV_A
    /\ LET a == DirectAddr(Mem(IP+1)) v == Mem(a) IN
       IF v = 0 THEN Fault(ERR_DIV_ZERO)
       ELSE LET r == CheckOp(A \div v) IN
            A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
            /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecDIV_67 == memory[IP] = OP_DIV_C
    /\ LET v == Mem(IP+1) IN
       IF v = 0 THEN Fault(ERR_DIV_ZERO)
       ELSE LET r == CheckOp(A \div v) IN
            A' = r[1] /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
            /\ UNCHANGED <<SP,DP,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

=============================================================================
