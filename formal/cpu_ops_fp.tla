--------------------------- MODULE cpu_ops_fp ---------------------------
(* FP operations: opcodes 128-162 *)
EXTENDS cpu_base

\* ===== FMOV: Load/Store (128-131) =====

\* FMOV FP, [addr] (128) — Load from direct address
ExecFMOV_128 == memory[IP] = OP_FMOV_FA
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                addr == DirectAddr(Mem(IP+2))
            IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE LET val == FPMemRead(addr, fmt)
                        new_val == FPWriteVal(phys, fmt, pos, val)
                    IN /\ FPSetRegs(phys, new_val)
                       /\ IP' = IP + 3
                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg,FPSR_reg>>

\* FMOV FP, [reg] (129) — Load via register indirect
ExecFMOV_129 == memory[IP] = OP_FMOV_FI
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                dec == DecodeIndirect(Mem(IP+2))
            IN IF ~dec[2] THEN Fault(dec[3])
               ELSE LET addr == dec[1]
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                       ELSE LET val == FPMemRead(addr, fmt)
                                new_val == FPWriteVal(phys, fmt, pos, val)
                            IN /\ FPSetRegs(phys, new_val)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg,FPSR_reg>>

\* FMOV [addr], FP (130) — Store to direct address
ExecFMOV_130 == memory[IP] = OP_FMOV_AF
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                addr == DirectAddr(Mem(IP+2))
                val == FPRead(phys, fmt, pos)
                byte_cnt == FPBytes(fmt)
            IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE LET b0 == val % 256
                        b1 == (val \div 256) % 256
                        b2 == (val \div 65536) % 256
                        b3 == (val \div 16777216) % 256
                    IN /\ IF byte_cnt = 4 THEN
                             memory' = [memory EXCEPT
                                 ![addr] = b0, ![addr+1] = b1,
                                 ![addr+2] = b2, ![addr+3] = b3]
                           ELSE IF byte_cnt = 2 THEN
                             memory' = [memory EXCEPT
                                 ![addr] = b0, ![addr+1] = b1]
                           ELSE \* byte_cnt = 1 (OFP8)
                             memory' = [memory EXCEPT ![addr] = b0]
                       /\ IP' = IP + 3
                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>

\* FMOV [reg], FP (131) — Store via register indirect
ExecFMOV_131 == memory[IP] = OP_FMOV_IF
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                dec == DecodeIndirect(Mem(IP+2))
            IN IF ~dec[2] THEN Fault(dec[3])
               ELSE LET addr == dec[1]
                        val == FPRead(phys, fmt, pos)
                        byte_cnt == FPBytes(fmt)
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                       ELSE LET b0 == val % 256
                                b1 == (val \div 256) % 256
                                b2 == (val \div 65536) % 256
                                b3 == (val \div 16777216) % 256
                            IN /\ IF byte_cnt = 4 THEN
                                     memory' = [memory EXCEPT
                                         ![addr] = b0, ![addr+1] = b1,
                                         ![addr+2] = b2, ![addr+3] = b3]
                                   ELSE IF byte_cnt = 2 THEN
                                     memory' = [memory EXCEPT
                                         ![addr] = b0, ![addr+1] = b1]
                                   ELSE \* byte_cnt = 1 (OFP8)
                                     memory' = [memory EXCEPT ![addr] = b0]
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>

\* ===== FP Arithmetic Helpers =====

\* Arithmetic ops verify structural behavior:
\* - FPM decode/validation, page boundary check
\* - NaN/Inf/Zero input detection (IEEE 754 Invalid, DivZero)
\* - Exception flags set in FPSR (sticky), default result produced
\* - Numeric result uses oracle (nondeterministic for TLC)

\* NaN propagation: if either input is NaN, result is qNaN
\* If sNaN, also raise Invalid
FPArithNaN(reg_val, mem_val, fmt) ==
    LET reg_nan == FP_isNaN(reg_val, fmt)
        mem_nan == FP_isNaN(mem_val, fmt)
        reg_snan == FP_isSNaN(reg_val, fmt)
        mem_snan == FP_isSNaN(mem_val, fmt)
        has_nan == reg_nan \/ mem_nan
        has_snan == reg_snan \/ mem_snan
    IN <<has_nan, has_snan>>

\* ===== FADD (132-133) =====

ExecFADD_132 == memory[IP] = OP_FADD_A
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                addr == DirectAddr(Mem(IP+2))
            IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE LET mem_val == FPMemRead(addr, fmt)
                        reg_val == FPRead(phys, fmt, pos)
                        nan_info == FPArithNaN(reg_val, mem_val, fmt)
                        has_nan == nan_info[1]
                        has_snan == nan_info[2]
                        inf_invalid == FP_isInf(reg_val, fmt) /\ FP_isInf(mem_val, fmt)
                                       /\ FP_sign(reg_val, fmt) # FP_sign(mem_val, fmt)
                        raised == IF has_snan \/ inf_invalid THEN {0} ELSE {}
                    IN IF has_nan \/ inf_invalid THEN
                            LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                            IN /\ FPSetRegs(phys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(phys, fmt, pos, result)
                                IN /\ FPSetRegs(phys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFADD_133 == memory[IP] = OP_FADD_I
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                dec == DecodeIndirect(Mem(IP+2))
            IN IF ~dec[2] THEN Fault(dec[3])
               ELSE LET addr == dec[1]
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                       ELSE LET mem_val == FPMemRead(addr, fmt)
                                reg_val == FPRead(phys, fmt, pos)
                                nan_info == FPArithNaN(reg_val, mem_val, fmt)
                                has_nan == nan_info[1]
                                has_snan == nan_info[2]
                                inf_invalid == FP_isInf(reg_val, fmt) /\ FP_isInf(mem_val, fmt)
                                               /\ FP_sign(reg_val, fmt) # FP_sign(mem_val, fmt)
                                raised == IF has_snan \/ inf_invalid THEN {0} ELSE {}
                            IN IF has_nan \/ inf_invalid THEN
                                    LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                                    IN /\ FPSetRegs(phys, new_val)
                                       /\ FPSR_reg' = FPSetFlags(raised)
                                       /\ IP' = IP + 3
                                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                               ELSE
                                    \E result \in FP_ORACLE:
                                        LET new_val == FPWriteVal(phys, fmt, pos, result)
                                        IN /\ FPSetRegs(phys, new_val)
                                           /\ FPSR_reg' = FPSetFlags({})
                                           /\ IP' = IP + 3
                                           /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FSUB (134-135) — same structure as FADD =====

ExecFSUB_134 == memory[IP] = OP_FSUB_A
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                addr == DirectAddr(Mem(IP+2))
            IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE LET mem_val == FPMemRead(addr, fmt)
                        reg_val == FPRead(phys, fmt, pos)
                        nan_info == FPArithNaN(reg_val, mem_val, fmt)
                        has_nan == nan_info[1]
                        has_snan == nan_info[2]
                        inf_invalid == FP_isInf(reg_val, fmt) /\ FP_isInf(mem_val, fmt)
                                       /\ FP_sign(reg_val, fmt) = FP_sign(mem_val, fmt)
                        raised == IF has_snan \/ inf_invalid THEN {0} ELSE {}
                    IN IF has_nan \/ inf_invalid THEN
                            LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                            IN /\ FPSetRegs(phys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(phys, fmt, pos, result)
                                IN /\ FPSetRegs(phys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFSUB_135 == memory[IP] = OP_FSUB_I
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                dec == DecodeIndirect(Mem(IP+2))
            IN IF ~dec[2] THEN Fault(dec[3])
               ELSE LET addr == dec[1]
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                       ELSE LET mem_val == FPMemRead(addr, fmt)
                                reg_val == FPRead(phys, fmt, pos)
                                nan_info == FPArithNaN(reg_val, mem_val, fmt)
                                has_nan == nan_info[1]
                                has_snan == nan_info[2]
                                inf_invalid == FP_isInf(reg_val, fmt) /\ FP_isInf(mem_val, fmt)
                                               /\ FP_sign(reg_val, fmt) = FP_sign(mem_val, fmt)
                                raised == IF has_snan \/ inf_invalid THEN {0} ELSE {}
                            IN IF has_nan \/ inf_invalid THEN
                                    LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                                    IN /\ FPSetRegs(phys, new_val)
                                       /\ FPSR_reg' = FPSetFlags(raised)
                                       /\ IP' = IP + 3
                                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                               ELSE
                                    \E result \in FP_ORACLE:
                                        LET new_val == FPWriteVal(phys, fmt, pos, result)
                                        IN /\ FPSetRegs(phys, new_val)
                                           /\ FPSR_reg' = FPSetFlags({})
                                           /\ IP' = IP + 3
                                           /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FMUL (136-137) =====

ExecFMUL_136 == memory[IP] = OP_FMUL_A
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                addr == DirectAddr(Mem(IP+2))
            IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE LET mem_val == FPMemRead(addr, fmt)
                        reg_val == FPRead(phys, fmt, pos)
                        nan_info == FPArithNaN(reg_val, mem_val, fmt)
                        has_nan == nan_info[1]
                        has_snan == nan_info[2]
                        zero_inf == (FP_isZero(reg_val, fmt) /\ FP_isInf(mem_val, fmt))
                                    \/ (FP_isInf(reg_val, fmt) /\ FP_isZero(mem_val, fmt))
                        raised == IF has_snan \/ zero_inf THEN {0} ELSE {}
                    IN IF has_nan \/ zero_inf THEN
                            LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                            IN /\ FPSetRegs(phys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(phys, fmt, pos, result)
                                IN /\ FPSetRegs(phys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFMUL_137 == memory[IP] = OP_FMUL_I
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                dec == DecodeIndirect(Mem(IP+2))
            IN IF ~dec[2] THEN Fault(dec[3])
               ELSE LET addr == dec[1]
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                       ELSE LET mem_val == FPMemRead(addr, fmt)
                                reg_val == FPRead(phys, fmt, pos)
                                nan_info == FPArithNaN(reg_val, mem_val, fmt)
                                has_nan == nan_info[1]
                                has_snan == nan_info[2]
                                zero_inf == (FP_isZero(reg_val, fmt) /\ FP_isInf(mem_val, fmt))
                                            \/ (FP_isInf(reg_val, fmt) /\ FP_isZero(mem_val, fmt))
                                raised == IF has_snan \/ zero_inf THEN {0} ELSE {}
                            IN IF has_nan \/ zero_inf THEN
                                    LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                                    IN /\ FPSetRegs(phys, new_val)
                                       /\ FPSR_reg' = FPSetFlags(raised)
                                       /\ IP' = IP + 3
                                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                               ELSE
                                    \E result \in FP_ORACLE:
                                        LET new_val == FPWriteVal(phys, fmt, pos, result)
                                        IN /\ FPSetRegs(phys, new_val)
                                           /\ FPSR_reg' = FPSetFlags({})
                                           /\ IP' = IP + 3
                                           /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FDIV (138-139) — also detects division by zero =====

ExecFDIV_138 == memory[IP] = OP_FDIV_A
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                addr == DirectAddr(Mem(IP+2))
            IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE LET mem_val == FPMemRead(addr, fmt)
                        reg_val == FPRead(phys, fmt, pos)
                        nan_info == FPArithNaN(reg_val, mem_val, fmt)
                        has_nan == nan_info[1]
                        has_snan == nan_info[2]
                        zero_zero == FP_isZero(reg_val, fmt) /\ FP_isZero(mem_val, fmt)
                        inf_inf == FP_isInf(reg_val, fmt) /\ FP_isInf(mem_val, fmt)
                        is_div_zero == ~FP_isNaN(reg_val, fmt) /\ ~FP_isInf(reg_val, fmt)
                                       /\ ~FP_isZero(reg_val, fmt) /\ FP_isZero(mem_val, fmt)
                        raised == (IF has_snan \/ zero_zero \/ inf_inf THEN {0} ELSE {})
                                  \cup (IF is_div_zero THEN {1} ELSE {})
                    IN IF has_nan \/ zero_zero \/ inf_inf THEN
                            LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                            IN /\ FPSetRegs(phys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE IF is_div_zero THEN
                            LET rsign == BitXor(FP_sign(reg_val, fmt), FP_sign(mem_val, fmt))
                                inf_result == IF rsign = 0 THEN FP_posInf(fmt) ELSE FP_negInf(fmt)
                                new_val == FPWriteVal(phys, fmt, pos, inf_result)
                            IN /\ FPSetRegs(phys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(phys, fmt, pos, result)
                                IN /\ FPSetRegs(phys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFDIV_139 == memory[IP] = OP_FDIV_I
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                dec == DecodeIndirect(Mem(IP+2))
            IN IF ~dec[2] THEN Fault(dec[3])
               ELSE LET addr == dec[1]
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                       ELSE LET mem_val == FPMemRead(addr, fmt)
                                reg_val == FPRead(phys, fmt, pos)
                                nan_info == FPArithNaN(reg_val, mem_val, fmt)
                                has_nan == nan_info[1]
                                has_snan == nan_info[2]
                                zero_zero == FP_isZero(reg_val, fmt) /\ FP_isZero(mem_val, fmt)
                                inf_inf == FP_isInf(reg_val, fmt) /\ FP_isInf(mem_val, fmt)
                                is_div_zero == ~FP_isNaN(reg_val, fmt) /\ ~FP_isInf(reg_val, fmt)
                                               /\ ~FP_isZero(reg_val, fmt) /\ FP_isZero(mem_val, fmt)
                                raised == (IF has_snan \/ zero_zero \/ inf_inf THEN {0} ELSE {})
                                          \cup (IF is_div_zero THEN {1} ELSE {})
                            IN IF has_nan \/ zero_zero \/ inf_inf THEN
                                    LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                                    IN /\ FPSetRegs(phys, new_val)
                                       /\ FPSR_reg' = FPSetFlags(raised)
                                       /\ IP' = IP + 3
                                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                               ELSE IF is_div_zero THEN
                                    LET rsign == BitXor(FP_sign(reg_val, fmt), FP_sign(mem_val, fmt))
                                        inf_result == IF rsign = 0 THEN FP_posInf(fmt) ELSE FP_negInf(fmt)
                                        new_val == FPWriteVal(phys, fmt, pos, inf_result)
                                    IN /\ FPSetRegs(phys, new_val)
                                       /\ FPSR_reg' = FPSetFlags(raised)
                                       /\ IP' = IP + 3
                                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                               ELSE
                                    \E result \in FP_ORACLE:
                                        LET new_val == FPWriteVal(phys, fmt, pos, result)
                                        IN /\ FPSetRegs(phys, new_val)
                                           /\ FPSR_reg' = FPSetFlags({})
                                           /\ IP' = IP + 3
                                           /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FCMP (140-141) — Sets Z and C_flag =====

ExecFCMP_140 == memory[IP] = OP_FCMP_A
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                addr == DirectAddr(Mem(IP+2))
            IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE LET mem_val == FPMemRead(addr, fmt)
                        reg_val == FPRead(phys, fmt, pos)
                        reg_nan == FP_isNaN(reg_val, fmt)
                        mem_nan == FP_isNaN(mem_val, fmt)
                        has_snan == FP_isSNaN(reg_val, fmt) \/ FP_isSNaN(mem_val, fmt)
                        raised == IF has_snan THEN {0} ELSE {}
                    IN IF reg_nan \/ mem_nan THEN
                            \* Unordered: Z=1, C=1
                            Z' = TRUE /\ C_flag' = TRUE
                            /\ FPSR_reg' = FPSetFlags(raised)
                            /\ IP' = IP + 3
                            /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                       ELSE
                            IF FP_isZero(reg_val, fmt) /\ FP_isZero(mem_val, fmt) THEN
                                Z' = TRUE /\ C_flag' = FALSE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                            ELSE IF reg_val = mem_val THEN
                                Z' = TRUE /\ C_flag' = FALSE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                            ELSE IF FP_less(reg_val, mem_val, fmt) THEN
                                Z' = FALSE /\ C_flag' = TRUE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                            ELSE
                                Z' = FALSE /\ C_flag' = FALSE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>

ExecFCMP_141 == memory[IP] = OP_FCMP_I
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                dec == DecodeIndirect(Mem(IP+2))
            IN IF ~dec[2] THEN Fault(dec[3])
               ELSE LET addr == dec[1]
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                       ELSE LET mem_val == FPMemRead(addr, fmt)
                                reg_val == FPRead(phys, fmt, pos)
                                reg_nan == FP_isNaN(reg_val, fmt)
                                mem_nan == FP_isNaN(mem_val, fmt)
                                has_snan == FP_isSNaN(reg_val, fmt) \/ FP_isSNaN(mem_val, fmt)
                                raised == IF has_snan THEN {0} ELSE {}
                            IN IF reg_nan \/ mem_nan THEN
                                    Z' = TRUE /\ C_flag' = TRUE
                                    /\ FPSR_reg' = FPSetFlags(raised)
                                    /\ IP' = IP + 3
                                    /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                               ELSE
                                    IF FP_isZero(reg_val, fmt) /\ FP_isZero(mem_val, fmt) THEN
                                        Z' = TRUE /\ C_flag' = FALSE
                                        /\ FPSR_reg' = FPSetFlags({})
                                        /\ IP' = IP + 3
                                        /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                                    ELSE IF reg_val = mem_val THEN
                                        Z' = TRUE /\ C_flag' = FALSE
                                        /\ FPSR_reg' = FPSetFlags({})
                                        /\ IP' = IP + 3
                                        /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                                    ELSE IF FP_less(reg_val, mem_val, fmt) THEN
                                        Z' = FALSE /\ C_flag' = TRUE
                                        /\ FPSR_reg' = FPSetFlags({})
                                        /\ IP' = IP + 3
                                        /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                                    ELSE
                                        Z' = FALSE /\ C_flag' = FALSE
                                        /\ FPSR_reg' = FPSetFlags({})
                                        /\ IP' = IP + 3
                                        /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>

\* ===== FABS (142) =====

ExecFABS_142 == memory[IP] = OP_FABS
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                val == FPRead(phys, fmt, pos)
                result == FP_clearSign(val, fmt)
                new_val == FPWriteVal(phys, fmt, pos, result)
            IN /\ FPSetRegs(phys, new_val)
               /\ IP' = IP + 2
               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg,FPSR_reg>>

\* ===== FNEG (143) =====

ExecFNEG_143 == memory[IP] = OP_FNEG
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                val == FPRead(phys, fmt, pos)
                result == FP_flipSign(val, fmt)
                new_val == FPWriteVal(phys, fmt, pos, result)
            IN /\ FPSetRegs(phys, new_val)
               /\ IP' = IP + 2
               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg,FPSR_reg>>

\* ===== FSQRT (144) =====

ExecFSQRT_144 == memory[IP] = OP_FSQRT
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                val == FPRead(phys, fmt, pos)
                width == FPWidth(fmt)
                sign_bit == 2^(width - 1)
                is_neg == val >= sign_bit /\ ~FP_isZero(val, fmt) /\ ~FP_isNaN(val, fmt)
                is_snan == FP_isSNaN(val, fmt)
                raised == IF is_neg \/ is_snan THEN {0} ELSE {}
            IN IF FP_isNaN(val, fmt) THEN
                    LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                    IN /\ FPSetRegs(phys, new_val)
                       /\ FPSR_reg' = FPSetFlags(raised)
                       /\ IP' = IP + 2
                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
               ELSE IF is_neg THEN
                    LET new_val == FPWriteVal(phys, fmt, pos, FP_qNaN(fmt))
                    IN /\ FPSetRegs(phys, new_val)
                       /\ FPSR_reg' = FPSetFlags(raised)
                       /\ IP' = IP + 2
                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
               ELSE IF FP_isZero(val, fmt) THEN
                    \* sqrt(+/-0) = +/-0
                    LET new_val == FPWriteVal(phys, fmt, pos, val)
                    IN /\ FPSetRegs(phys, new_val)
                       /\ FPSR_reg' = FPSetFlags({})
                       /\ IP' = IP + 2
                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
               ELSE IF FP_isInf(val, fmt) THEN
                    \* sqrt(+Inf) = +Inf (negative already handled above)
                    LET new_val == FPWriteVal(phys, fmt, pos, val)
                    IN /\ FPSetRegs(phys, new_val)
                       /\ FPSR_reg' = FPSetFlags({})
                       /\ IP' = IP + 2
                       /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
               ELSE
                    \E result \in FP_ORACLE:
                        LET new_val == FPWriteVal(phys, fmt, pos, result)
                        IN /\ FPSetRegs(phys, new_val)
                           /\ FPSR_reg' = FPSetFlags({})
                           /\ IP' = IP + 2
                           /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FMOV_RR (145) — Register-to-Register Copy =====

ExecFMOV_RR_145 == memory[IP] = OP_FMOV_RR
    /\ LET dst_fpm == Mem(IP+1) src_fpm == Mem(IP+2)
           dv == ValidateFPM(dst_fpm)
           sv == ValidateFPM(src_fpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET dst_fmt == FPM_fmt(dst_fpm) dst_pos == FPM_pos(dst_fpm)
                   dphys == FPM_phys(dst_fpm)
                   src_fmt == FPM_fmt(src_fpm) src_pos == FPM_pos(src_fpm)
                   sphys == FPM_phys(src_fpm)
               IN IF dst_fmt # src_fmt THEN Fault(ERR_FP_FORMAT)
                  ELSE LET src_val == FPRead(sphys, src_fmt, src_pos)
                           new_val == FPWriteVal(dphys, dst_fmt, dst_pos, src_val)
                       IN /\ FPSetRegs(dphys, new_val)
                          /\ IP' = IP + 3
                          /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg,FPSR_reg>>

\* ===== FCVT (146) — Format Conversion =====

ExecFCVT_146 == memory[IP] = OP_FCVT
    /\ LET dst_fpm == Mem(IP+1) src_fpm == Mem(IP+2)
           dv == ValidateFPM(dst_fpm)
           sv == ValidateFPM(src_fpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET dst_fmt == FPM_fmt(dst_fpm) dst_pos == FPM_pos(dst_fpm)
                   dphys == FPM_phys(dst_fpm)
                   src_fmt == FPM_fmt(src_fpm) src_pos == FPM_pos(src_fpm)
                   sphys == FPM_phys(src_fpm)
                   src_val == FPRead(sphys, src_fmt, src_pos)
                   is_snan == FP_isSNaN(src_val, src_fmt)
                   raised == IF is_snan THEN {0} ELSE {}
               IN IF FP_isNaN(src_val, src_fmt) THEN
                       LET new_val == FPWriteVal(dphys, dst_fmt, dst_pos, FP_qNaN(dst_fmt))
                       IN /\ FPSetRegs(dphys, new_val)
                          /\ FPSR_reg' = FPSetFlags(raised)
                          /\ IP' = IP + 3
                          /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                  ELSE
                       \* Conversion: result is oracle, may raise OF/UF/NX
                       \E result \in FP_ORACLE:
                           \E cvt_flags \in SUBSET {2, 3, 4}:
                               LET new_val == FPWriteVal(dphys, dst_fmt, dst_pos, result)
                               IN /\ FPSetRegs(dphys, new_val)
                                  /\ FPSR_reg' = FPSetFlags(cvt_flags)
                                  /\ IP' = IP + 3
                                  /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FITOF (147) — Integer to FP =====

ExecFITOF_147 == memory[IP] = OP_FITOF
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                gpr == Mem(IP+2)
            IN IF gpr > 3 THEN Fault(ERR_INVALID_REG)
               ELSE LET int_val == RegValue(gpr)
                    IN \* uint8 to FP: result oracle, may set NX
                       \E result \in FP_ORACLE:
                           LET new_val == FPWriteVal(phys, fmt, pos, result)
                           IN /\ FPSetRegs(phys, new_val)
                              /\ (\/ FPSR_reg' = FPSetFlags({4})
                                  \/ FPSR_reg' = FPSR_reg)
                              /\ IP' = IP + 3
                              /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FFTOI (148) — FP to Integer =====

ExecFFTOI_148 == memory[IP] = OP_FFTOI
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm)
                gpr == Mem(IP+2)
            IN IF gpr > 3 THEN Fault(ERR_INVALID_REG)
               ELSE LET fp_val == FPRead(phys, fmt, pos)
                        is_nan == FP_isNaN(fp_val, fmt)
                        is_inf == FP_isInf(fp_val, fmt)
                        is_snan == FP_isSNaN(fp_val, fmt)
                        raised == IF is_nan \/ is_inf THEN {0} ELSE {}
                    IN \E int_result \in FP_ORACLE:
                                SetRegABCD(gpr, int_result)
                                /\ SP' = SP /\ DP' = DP
                                /\ FPSR_reg' = FPSetFlags(raised)
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg>>

\* ===== FSTAT (149) — Read FPSR -> GPR =====

ExecFSTAT_149 == memory[IP] = OP_FSTAT
    /\ LET gpr == Mem(IP+1) IN
       IF gpr > 3 THEN Fault(ERR_INVALID_REG)
       ELSE SetRegABCD(gpr, FPSR_reg)
            /\ SP' = SP /\ DP' = DP
            /\ IP' = IP + 2
            /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>

\* ===== FCFG (150) — Read FPCR -> GPR =====

ExecFCFG_150 == memory[IP] = OP_FCFG
    /\ LET gpr == Mem(IP+1) IN
       IF gpr > 3 THEN Fault(ERR_INVALID_REG)
       ELSE SetRegABCD(gpr, FPCR_reg)
            /\ SP' = SP /\ DP' = DP
            /\ IP' = IP + 2
            /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>

\* ===== FSCFG (151) — Write GPR -> FPCR =====

ExecFSCFG_151 == memory[IP] = OP_FSCFG
    /\ LET gpr == Mem(IP+1) IN
       IF gpr > 3 THEN Fault(ERR_INVALID_REG)
       ELSE LET val == RegValue(gpr)
            IN FPCR_reg' = val % 4  \* Only RM bits [1:0]; rest reserved
               /\ IP' = IP + 2
               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FA_reg,FB_reg,FPSR_reg>>

\* ===== FCLR (152) — Clear FPSR =====

ExecFCLR_152 == memory[IP] = OP_FCLR
    /\ FPSR_reg' = 0 /\ IP' = IP + 1
    /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg>>

\* ===== Reg-Reg Arithmetic (153-157) =====

ExecFADD_RR_153 == memory[IP] = OP_FADD_RR
    /\ LET dfpm == Mem(IP+1) sfpm == Mem(IP+2)
           dv == ValidateFPM(dfpm) sv == ValidateFPM(sfpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET df == FPM_fmt(dfpm) sf == FPM_fmt(sfpm)
               IN IF df # sf THEN Fault(ERR_FP_FORMAT)
               ELSE LET fmt == df
                        dp == FPM_pos(dfpm) sp == FPM_pos(sfpm)
                        dphys == FPM_phys(dfpm) sphys == FPM_phys(sfpm)
                        dst_val == FPRead(dphys, fmt, dp) src_val == FPRead(sphys, fmt, sp)
                        nan_info == FPArithNaN(dst_val, src_val, fmt)
                        has_nan == nan_info[1] has_snan == nan_info[2]
                        inf_invalid == FP_isInf(dst_val, fmt) /\ FP_isInf(src_val, fmt)
                                       /\ FP_sign(dst_val, fmt) # FP_sign(src_val, fmt)
                        raised == IF has_snan \/ inf_invalid THEN {0} ELSE {}
                    IN IF has_nan \/ inf_invalid THEN
                            LET new_val == FPWriteVal(dphys, fmt, dp, FP_qNaN(fmt))
                            IN /\ FPSetRegs(dphys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(dphys, fmt, dp, result)
                                IN /\ FPSetRegs(dphys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFSUB_RR_154 == memory[IP] = OP_FSUB_RR
    /\ LET dfpm == Mem(IP+1) sfpm == Mem(IP+2)
           dv == ValidateFPM(dfpm) sv == ValidateFPM(sfpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET df == FPM_fmt(dfpm) sf == FPM_fmt(sfpm)
               IN IF df # sf THEN Fault(ERR_FP_FORMAT)
               ELSE LET fmt == df
                        dp == FPM_pos(dfpm) sp == FPM_pos(sfpm)
                        dphys == FPM_phys(dfpm) sphys == FPM_phys(sfpm)
                        dst_val == FPRead(dphys, fmt, dp) src_val == FPRead(sphys, fmt, sp)
                        nan_info == FPArithNaN(dst_val, src_val, fmt)
                        has_nan == nan_info[1] has_snan == nan_info[2]
                        inf_invalid == FP_isInf(dst_val, fmt) /\ FP_isInf(src_val, fmt)
                                       /\ FP_sign(dst_val, fmt) = FP_sign(src_val, fmt)
                        raised == IF has_snan \/ inf_invalid THEN {0} ELSE {}
                    IN IF has_nan \/ inf_invalid THEN
                            LET new_val == FPWriteVal(dphys, fmt, dp, FP_qNaN(fmt))
                            IN /\ FPSetRegs(dphys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(dphys, fmt, dp, result)
                                IN /\ FPSetRegs(dphys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFMUL_RR_155 == memory[IP] = OP_FMUL_RR
    /\ LET dfpm == Mem(IP+1) sfpm == Mem(IP+2)
           dv == ValidateFPM(dfpm) sv == ValidateFPM(sfpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET df == FPM_fmt(dfpm) sf == FPM_fmt(sfpm)
               IN IF df # sf THEN Fault(ERR_FP_FORMAT)
               ELSE LET fmt == df
                        dp == FPM_pos(dfpm) sp == FPM_pos(sfpm)
                        dphys == FPM_phys(dfpm) sphys == FPM_phys(sfpm)
                        dst_val == FPRead(dphys, fmt, dp) src_val == FPRead(sphys, fmt, sp)
                        nan_info == FPArithNaN(dst_val, src_val, fmt)
                        has_nan == nan_info[1] has_snan == nan_info[2]
                        zero_inf == (FP_isZero(dst_val, fmt) /\ FP_isInf(src_val, fmt))
                                    \/ (FP_isInf(dst_val, fmt) /\ FP_isZero(src_val, fmt))
                        raised == IF has_snan \/ zero_inf THEN {0} ELSE {}
                    IN IF has_nan \/ zero_inf THEN
                            LET new_val == FPWriteVal(dphys, fmt, dp, FP_qNaN(fmt))
                            IN /\ FPSetRegs(dphys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(dphys, fmt, dp, result)
                                IN /\ FPSetRegs(dphys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFDIV_RR_156 == memory[IP] = OP_FDIV_RR
    /\ LET dfpm == Mem(IP+1) sfpm == Mem(IP+2)
           dv == ValidateFPM(dfpm) sv == ValidateFPM(sfpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET df == FPM_fmt(dfpm) sf == FPM_fmt(sfpm)
               IN IF df # sf THEN Fault(ERR_FP_FORMAT)
               ELSE LET fmt == df
                        dp == FPM_pos(dfpm) sp == FPM_pos(sfpm)
                        dphys == FPM_phys(dfpm) sphys == FPM_phys(sfpm)
                        dst_val == FPRead(dphys, fmt, dp) src_val == FPRead(sphys, fmt, sp)
                        nan_info == FPArithNaN(dst_val, src_val, fmt)
                        has_nan == nan_info[1] has_snan == nan_info[2]
                        zero_zero == FP_isZero(dst_val, fmt) /\ FP_isZero(src_val, fmt)
                        inf_inf == FP_isInf(dst_val, fmt) /\ FP_isInf(src_val, fmt)
                        is_div_zero == ~FP_isNaN(dst_val, fmt) /\ ~FP_isInf(dst_val, fmt)
                                       /\ ~FP_isZero(dst_val, fmt) /\ FP_isZero(src_val, fmt)
                        raised == (IF has_snan \/ zero_zero \/ inf_inf THEN {0} ELSE {})
                                  \cup (IF is_div_zero THEN {1} ELSE {})
                    IN IF has_nan \/ zero_zero \/ inf_inf THEN
                            LET new_val == FPWriteVal(dphys, fmt, dp, FP_qNaN(fmt))
                            IN /\ FPSetRegs(dphys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE IF is_div_zero THEN
                            LET rsign == BitXor(FP_sign(dst_val, fmt), FP_sign(src_val, fmt))
                                inf_result == IF rsign = 0 THEN FP_posInf(fmt) ELSE FP_negInf(fmt)
                                new_val == FPWriteVal(dphys, fmt, dp, inf_result)
                            IN /\ FPSetRegs(dphys, new_val)
                               /\ FPSR_reg' = FPSetFlags(raised)
                               /\ IP' = IP + 3
                               /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                       ELSE
                            \E result \in FP_ORACLE:
                                LET new_val == FPWriteVal(dphys, fmt, dp, result)
                                IN /\ FPSetRegs(dphys, new_val)
                                   /\ FPSR_reg' = FPSetFlags({})
                                   /\ IP' = IP + 3
                                   /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFCMP_RR_157 == memory[IP] = OP_FCMP_RR
    /\ LET dfpm == Mem(IP+1) sfpm == Mem(IP+2)
           dv == ValidateFPM(dfpm) sv == ValidateFPM(sfpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET df == FPM_fmt(dfpm) sf == FPM_fmt(sfpm)
               IN IF df # sf THEN Fault(ERR_FP_FORMAT)
               ELSE LET fmt == df
                        dp == FPM_pos(dfpm) sp == FPM_pos(sfpm)
                        dphys == FPM_phys(dfpm) sphys == FPM_phys(sfpm)
                        dst_val == FPRead(dphys, fmt, dp) src_val == FPRead(sphys, fmt, sp)
                        reg_nan == FP_isNaN(dst_val, fmt)
                        src_nan == FP_isNaN(src_val, fmt)
                        has_snan == FP_isSNaN(dst_val, fmt) \/ FP_isSNaN(src_val, fmt)
                        raised == IF has_snan THEN {0} ELSE {}
                    IN IF reg_nan \/ src_nan THEN
                            Z' = TRUE /\ C_flag' = TRUE
                            /\ FPSR_reg' = FPSetFlags(raised)
                            /\ IP' = IP + 3
                            /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                       ELSE
                            IF FP_isZero(dst_val, fmt) /\ FP_isZero(src_val, fmt) THEN
                                Z' = TRUE /\ C_flag' = FALSE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                            ELSE IF dst_val = src_val THEN
                                Z' = TRUE /\ C_flag' = FALSE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                            ELSE IF FP_less(dst_val, src_val, fmt) THEN
                                Z' = FALSE /\ C_flag' = TRUE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>
                            ELSE
                                Z' = FALSE /\ C_flag' = FALSE
                                /\ FPSR_reg' = FPSetFlags({})
                                /\ IP' = IP + 3
                                /\ UNCHANGED <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FB_reg,FPCR_reg>>

\* ===== FCLASS (158) =====

ExecFCLASS_158 == memory[IP] = OP_FCLASS
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm) gpr == Mem(IP+2) IN
            IF gpr > 3 THEN Fault(ERR_INVALID_REG)
            ELSE LET val == FPRead(phys, fmt, pos)
                     cls == FPClassify(val, fmt)
                 IN SetRegABCD(gpr, cls)
                    /\ SP' = SP /\ DP' = DP
                    /\ IP' = IP + 3
                    /\ UNCHANGED <<Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>

\* ===== FMADD (159-160) — Fused Multiply-Add =====
\* dst = src * mem[addr] + dst

ExecFMADD_A_159 == memory[IP] = OP_FMADD_A
    /\ LET dfpm == Mem(IP+1) sfpm == Mem(IP+2)
           dv == ValidateFPM(dfpm) sv == ValidateFPM(sfpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET df == FPM_fmt(dfpm) sf == FPM_fmt(sfpm)
               IN IF df # sf THEN Fault(ERR_FP_FORMAT)
               ELSE LET fmt == df
                        dp == FPM_pos(dfpm) sp == FPM_pos(sfpm)
                        dphys == FPM_phys(dfpm) sphys == FPM_phys(sfpm)
                        addr == DirectAddr(Mem(IP+3))
                    IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                    ELSE LET dst_val == FPRead(dphys, fmt, dp)
                             src_val == FPRead(sphys, fmt, sp)
                             mem_val == FPMemRead(addr, fmt)
                             has_nan == FP_isNaN(dst_val,fmt) \/ FP_isNaN(src_val,fmt)
                                        \/ FP_isNaN(mem_val,fmt)
                             has_snan == FP_isSNaN(dst_val,fmt) \/ FP_isSNaN(src_val,fmt)
                                         \/ FP_isSNaN(mem_val,fmt)
                             inf_zero == (FP_isInf(src_val,fmt) /\ FP_isZero(mem_val,fmt))
                                         \/ (FP_isZero(src_val,fmt) /\ FP_isInf(mem_val,fmt))
                             raised == IF has_snan \/ inf_zero THEN {0} ELSE {}
                         IN IF has_nan \/ inf_zero THEN
                                 LET new_val == FPWriteVal(dphys, fmt, dp, FP_qNaN(fmt))
                                 IN /\ FPSetRegs(dphys, new_val)
                                    /\ FPSR_reg' = FPSetFlags(raised)
                                    /\ IP' = IP + 4
                                    /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                            ELSE \E result \in FP_ORACLE:
                                 LET new_val == FPWriteVal(dphys, fmt, dp, result)
                                 IN /\ FPSetRegs(dphys, new_val)
                                    /\ FPSR_reg' = FPSetFlags({})
                                    /\ IP' = IP + 4
                                    /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

ExecFMADD_I_160 == memory[IP] = OP_FMADD_I
    /\ LET dfpm == Mem(IP+1) sfpm == Mem(IP+2)
           dv == ValidateFPM(dfpm) sv == ValidateFPM(sfpm)
       IN IF dv # 0 THEN Fault(dv)
          ELSE IF sv # 0 THEN Fault(sv)
          ELSE LET df == FPM_fmt(dfpm) sf == FPM_fmt(sfpm)
               IN IF df # sf THEN Fault(ERR_FP_FORMAT)
               ELSE LET fmt == df
                        dp == FPM_pos(dfpm) sp == FPM_pos(sfpm)
                        dphys == FPM_phys(dfpm) sphys == FPM_phys(sfpm)
                        dec == DecodeIndirect(Mem(IP+3))
                    IN IF ~dec[2] THEN Fault(dec[3])
                    ELSE LET addr == dec[1]
                         IN IF ~FPPageOk(addr, fmt) THEN Fault(ERR_PAGE_BOUNDARY)
                         ELSE LET dst_val == FPRead(dphys, fmt, dp)
                                  src_val == FPRead(sphys, fmt, sp)
                                  mem_val == FPMemRead(addr, fmt)
                                  has_nan == FP_isNaN(dst_val,fmt) \/ FP_isNaN(src_val,fmt)
                                             \/ FP_isNaN(mem_val,fmt)
                                  has_snan == FP_isSNaN(dst_val,fmt) \/ FP_isSNaN(src_val,fmt)
                                              \/ FP_isSNaN(mem_val,fmt)
                                  inf_zero == (FP_isInf(src_val,fmt) /\ FP_isZero(mem_val,fmt))
                                              \/ (FP_isZero(src_val,fmt) /\ FP_isInf(mem_val,fmt))
                                  raised == IF has_snan \/ inf_zero THEN {0} ELSE {}
                              IN IF has_nan \/ inf_zero THEN
                                      LET new_val == FPWriteVal(dphys, fmt, dp, FP_qNaN(fmt))
                                      IN /\ FPSetRegs(dphys, new_val)
                                         /\ FPSR_reg' = FPSetFlags(raised)
                                         /\ IP' = IP + 4
                                         /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>
                                 ELSE \E result \in FP_ORACLE:
                                      LET new_val == FPWriteVal(dphys, fmt, dp, result)
                                      IN /\ FPSetRegs(dphys, new_val)
                                         /\ FPSR_reg' = FPSetFlags({})
                                         /\ IP' = IP + 4
                                         /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg>>

\* ===== FMOV Immediate (161-162) =====

\* FMOV FP, imm8 (161) — Load 8-bit immediate into FP sub-register
ExecFMOV_161 == memory[IP] = OP_FMOV_FI8
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm) IN
            IF fmt \notin {3, 4} THEN Fault(ERR_FP_FORMAT)
            ELSE LET imm8 == Mem(IP+2)
                     new_val == FPWriteVal(phys, fmt, pos, imm8)
                 IN /\ FPSetRegs(phys, new_val)
                    /\ IP' = IP + 3
                    /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg,FPSR_reg>>

\* FMOV FP, imm16 (162) — Load 16-bit immediate into FP sub-register
ExecFMOV_162 == memory[IP] = OP_FMOV_FI16
    /\ LET fpm == Mem(IP+1) fv == ValidateFPM(fpm) IN
       IF fv # 0 THEN Fault(fv)
       ELSE LET fmt == FPM_fmt(fpm) pos == FPM_pos(fpm) phys == FPM_phys(fpm) IN
            IF fmt \notin {1, 2} THEN Fault(ERR_FP_FORMAT)
            ELSE LET imm16 == Mem(IP+2) + Mem(IP+3) * 256
                     new_val == FPWriteVal(phys, fmt, pos, imm16)
                 IN /\ FPSetRegs(phys, new_val)
                    /\ IP' = IP + 4
                    /\ UNCHANGED <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FPCR_reg,FPSR_reg>>

=============================================================================
