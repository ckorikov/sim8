--------------------------- MODULE cpu_ops_jump ---------------------------
(* JMP operations: 30-31, conditional jumps 32-43 *)
EXTENDS cpu_base

\* JMP (30-31)
ExecJMP_30 == memory[IP] = OP_JMP_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IP' = RegValue(reg) /\ UNCHANGED unch_jump

ExecJMP_31 == memory[IP] = OP_JMP
    /\ IP' = Mem(IP+1)
    /\ UNCHANGED unch_jump

\* JC - Jump if Carry (32-33)
ExecJC_32 == memory[IP] = OP_JC_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IP' = (IF C_flag THEN RegValue(reg) ELSE IP + 2) /\ UNCHANGED unch_jump

ExecJC_33 == memory[IP] = OP_JC
    /\ IP' = (IF C_flag THEN Mem(IP+1) ELSE IP + 2)
    /\ UNCHANGED unch_jump

\* JNC - Jump if No Carry (34-35)
ExecJNC_34 == memory[IP] = OP_JNC_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IP' = (IF ~C_flag THEN RegValue(reg) ELSE IP + 2) /\ UNCHANGED unch_jump

ExecJNC_35 == memory[IP] = OP_JNC
    /\ IP' = (IF ~C_flag THEN Mem(IP+1) ELSE IP + 2)
    /\ UNCHANGED unch_jump

\* JZ - Jump if Zero (36-37)
ExecJZ_36 == memory[IP] = OP_JZ_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IP' = (IF Z THEN RegValue(reg) ELSE IP + 2) /\ UNCHANGED unch_jump

ExecJZ_37 == memory[IP] = OP_JZ
    /\ IP' = (IF Z THEN Mem(IP+1) ELSE IP + 2)
    /\ UNCHANGED unch_jump

\* JNZ - Jump if Not Zero (38-39)
ExecJNZ_38 == memory[IP] = OP_JNZ_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IP' = (IF ~Z THEN RegValue(reg) ELSE IP + 2) /\ UNCHANGED unch_jump

ExecJNZ_39 == memory[IP] = OP_JNZ
    /\ IP' = (IF ~Z THEN Mem(IP+1) ELSE IP + 2)
    /\ UNCHANGED unch_jump

\* JA - Jump if Above (not carry and not zero) (40-41)
ExecJA_40 == memory[IP] = OP_JA_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IP' = (IF (~C_flag /\ ~Z) THEN RegValue(reg) ELSE IP + 2) /\ UNCHANGED unch_jump

ExecJA_41 == memory[IP] = OP_JA
    /\ IP' = (IF (~C_flag /\ ~Z) THEN Mem(IP+1) ELSE IP + 2)
    /\ UNCHANGED unch_jump

\* JNA - Jump if Not Above (carry or zero) (42-43)
ExecJNA_42 == memory[IP] = OP_JNA_R
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IP' = (IF (C_flag \/ Z) THEN RegValue(reg) ELSE IP + 2) /\ UNCHANGED unch_jump

ExecJNA_43 == memory[IP] = OP_JNA
    /\ IP' = (IF (C_flag \/ Z) THEN Mem(IP+1) ELSE IP + 2)
    /\ UNCHANGED unch_jump

=============================================================================
