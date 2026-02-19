--------------------------- MODULE cpu_ops_mov ---------------------------
(* MOV operations: 1-8 *)
EXTENDS cpu_base

ExecMOV_1 == memory[IP] = OP_MOV_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..5 \/ s \notin 0..5 THEN Fault(ERR_INVALID_REG)
       ELSE SetReg(d, RegValue(s)) /\ IP' = IP + 3
            /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMOV_2 == memory[IP] = OP_MOV_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..5 THEN Fault(ERR_INVALID_REG)
       ELSE SetReg(d, Mem(a)) /\ IP' = IP + 3
            /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMOV_3 == memory[IP] = OP_MOV_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..5 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE SetReg(d, Mem(dec[1])) /\ IP' = IP + 3
            /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMOV_4 == memory[IP] = OP_MOV_AR
    /\ LET a == DirectAddr(Mem(IP+1)) s == Mem(IP+2) IN
       IF s \notin 0..5 THEN Fault(ERR_INVALID_REG)
       ELSE memory' = [memory EXCEPT ![a] = RegValue(s)] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMOV_5 == memory[IP] = OP_MOV_IR
    /\ LET dec == DecodeIndirect(Mem(IP+1)) s == Mem(IP+2) IN
       IF ~dec[2] THEN Fault(dec[3])
       ELSE IF s \notin 0..5 THEN Fault(ERR_INVALID_REG)
       ELSE memory' = [memory EXCEPT ![dec[1]] = RegValue(s)] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMOV_6 == memory[IP] = OP_MOV_RC
    /\ LET d == Mem(IP+1) v == Mem(IP+2) IN
       IF d \notin 0..5 THEN Fault(ERR_INVALID_REG)
       ELSE SetReg(d, v) /\ IP' = IP + 3
            /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMOV_7 == memory[IP] = OP_MOV_AC
    /\ LET a == DirectAddr(Mem(IP+1)) v == Mem(IP+2) IN
       memory' = [memory EXCEPT ![a] = v] /\ IP' = IP + 3
       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,state,FA_reg,FPCR_reg,FPSR_reg>>

ExecMOV_8 == memory[IP] = OP_MOV_IC
    /\ LET dec == DecodeIndirect(Mem(IP+1)) v == Mem(IP+2) IN
       IF ~dec[2] THEN Fault(dec[3])
       ELSE memory' = [memory EXCEPT ![dec[1]] = v] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,state,FA_reg,FPCR_reg,FPSR_reg>>

=============================================================================
