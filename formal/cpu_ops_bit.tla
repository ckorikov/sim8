--------------------------- MODULE cpu_ops_bit ---------------------------
(* Bitwise operations: AND 70-73, OR 74-77, XOR 78-81, NOT 82, SHL 90-93, SHR 94-97 *)
EXTENDS cpu_base

\* AND (70-73)
ExecAND_70 == memory[IP] = OP_AND_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..3 \/ s \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitAnd(RegValue(d), RegValue(s)) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecAND_71 == memory[IP] = OP_AND_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET r == BitAnd(RegValue(d), Mem(dec[1])) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecAND_72 == memory[IP] = OP_AND_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitAnd(RegValue(d), Mem(a)) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecAND_73 == memory[IP] = OP_AND_RC
    /\ LET d == Mem(IP+1) v == Mem(IP+2) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitAnd(RegValue(d), v) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

\* OR (74-77)
ExecOR_74 == memory[IP] = OP_OR_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..3 \/ s \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitOr(RegValue(d), RegValue(s)) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecOR_75 == memory[IP] = OP_OR_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET r == BitOr(RegValue(d), Mem(dec[1])) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecOR_76 == memory[IP] = OP_OR_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitOr(RegValue(d), Mem(a)) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecOR_77 == memory[IP] = OP_OR_RC
    /\ LET d == Mem(IP+1) v == Mem(IP+2) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitOr(RegValue(d), v) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

\* XOR (78-81)
ExecXOR_78 == memory[IP] = OP_XOR_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..3 \/ s \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitXor(RegValue(d), RegValue(s)) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecXOR_79 == memory[IP] = OP_XOR_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET r == BitXor(RegValue(d), Mem(dec[1])) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecXOR_80 == memory[IP] = OP_XOR_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitXor(RegValue(d), Mem(a)) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecXOR_81 == memory[IP] = OP_XOR_RC
    /\ LET d == Mem(IP+1) v == Mem(IP+2) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitXor(RegValue(d), v) IN
            SetRegNoSP(d, r) /\ Z' = (r = 0) /\ UNCHANGED C_flag /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

\* NOT (82)
ExecNOT_82 == memory[IP] = OP_NOT
    /\ LET reg == Mem(IP+1) IN
       IF reg \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == BitNot(RegValue(reg)) IN
            SetRegNoSP(reg, r) /\ UNCHANGED C_flag /\ Z' = (r = 0) /\ IP' = IP + 2
            /\ UNCHANGED <<SP,DP,F,memory,state>>

\* SHL (90-93) - shift left (ARM-style carry)
ExecSHL_90 == memory[IP] = OP_SHL_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..3 \/ s \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET cnt == RegValue(s) r == CheckSHL(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecSHL_91 == memory[IP] = OP_SHL_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET cnt == Mem(dec[1]) r == CheckSHL(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecSHL_92 == memory[IP] = OP_SHL_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET cnt == Mem(a) r == CheckSHL(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecSHL_93 == memory[IP] = OP_SHL_RC
    /\ LET d == Mem(IP+1) cnt == Mem(IP+2) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckSHL(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

\* SHR (94-97) - shift right (ARM-style carry: C=1 if bits shifted out)
ExecSHR_94 == memory[IP] = OP_SHR_RR
    /\ LET d == Mem(IP+1) s == Mem(IP+2) IN
       IF d \notin 0..3 \/ s \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET cnt == RegValue(s) r == CheckSHR(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecSHR_95 == memory[IP] = OP_SHR_RI
    /\ LET d == Mem(IP+1) dec == DecodeIndirect(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE IF ~dec[2] THEN Fault(dec[3])
       ELSE LET cnt == Mem(dec[1]) r == CheckSHR(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecSHR_96 == memory[IP] = OP_SHR_RA
    /\ LET d == Mem(IP+1) a == DirectAddr(Mem(IP+2)) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET cnt == Mem(a) r == CheckSHR(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

ExecSHR_97 == memory[IP] = OP_SHR_RC
    /\ LET d == Mem(IP+1) cnt == Mem(IP+2) IN
       IF d \notin 0..3 THEN Fault(ERR_INVALID_REG)
       ELSE LET r == CheckSHR(RegValue(d), cnt) IN
            SetRegNoSP(d, r[1]) /\ C_flag' = (IF cnt = 0 THEN C_flag ELSE r[2]) /\ Z' = r[3] /\ IP' = IP + 3
            /\ UNCHANGED <<SP,DP,F,memory,state>>

=============================================================================
