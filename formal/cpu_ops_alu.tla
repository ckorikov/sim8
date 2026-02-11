--------------------------- MODULE cpu_ops_alu ---------------------------
(* ALU operations: ADD 10-13, SUB 14-17, INC 18, DEC 19, CMP 20-23 *)
EXTENDS cpu_base

\* ADD (10-13)
ExecADD_10 == memory[IP] = OP_ADD_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..4 \/ s \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) + RegValue(s)) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

ExecADD_11 == memory[IP] = OP_ADD_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET r == CheckOp(RegValue(d) + Mem(dec[1])) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

ExecADD_12 == memory[IP] = OP_ADD_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) + Mem(a)) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

ExecADD_13 == memory[IP] = OP_ADD_RC
    /\ LET d == Mem(IP+1) v == Mem(IP+2) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) + v) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

\* SUB (14-17)
ExecSUB_14 == memory[IP] = OP_SUB_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..4 \/ s \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) - RegValue(s)) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

ExecSUB_15 == memory[IP] = OP_SUB_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET r == CheckOp(RegValue(d) - Mem(dec[1])) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

ExecSUB_16 == memory[IP] = OP_SUB_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) - Mem(a)) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

ExecSUB_17 == memory[IP] = OP_SUB_RC
    /\ LET d == Mem(IP+1) v == Mem(IP+2) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) - v) IN
            SetReg(d, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_alu

\* INC/DEC (18-19)
ExecINC == memory[IP] = OP_INC
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(reg) + 1) IN
            SetReg(reg, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
            /\ UNCHANGED unch_alu

ExecDEC == memory[IP] = OP_DEC
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(reg) - 1) IN
            SetReg(reg, r[1]) /\ C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 2
            /\ UNCHANGED unch_alu

\* CMP (20-23)
ExecCMP_20 == memory[IP] = OP_CMP_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..4 \/ s \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) - RegValue(s)) IN
            C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_cmp

ExecCMP_21 == memory[IP] = OP_CMP_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET r == CheckOp(RegValue(d) - Mem(dec[1])) IN
            C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_cmp

ExecCMP_22 == memory[IP] = OP_CMP_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) - Mem(a)) IN
            C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_cmp

ExecCMP_23 == memory[IP] = OP_CMP_RC
    /\ LET d == Mem(IP+1) v == Mem(IP+2) IN
       IF d \notin 0..4 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckOp(RegValue(d) - v) IN
            C_flag' = r[2] /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED unch_cmp

=============================================================================
