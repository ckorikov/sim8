------------------------- MODULE cpu_ops_matrix -------------------------
(*
   Matrix Unit instruction handlers (v3)
   Synchronous: MSET, MFSTAT, MFCLR, MWAIT
   Asynchronous: MMUL, MMAD (pushed to mu_queue)
   MU execution: MuStep (interleaved with CPU)

   Spec references:
     spec/matrix.md §11.2  — MU registers (MA/MB/MC/MM/MN/MK/MFPSR)
     spec/matrix.md §11.3  — Properties (queue, formats, auto-increment)
     spec/matrix.md §11.4  — Instructions (MSET/MFSTAT/MFCLR/MWAIT/MMUL/MMAD)
     spec/matrix.md §11.5  — Faults (ERR_VU_FORMAT, ERR_VU_OOB, ERR_INVALID_REG)
     spec/errors.md        — ERR_VU_OOB (13), ERR_VU_FORMAT (14), ERR_INVALID_REG (4)
*)

EXTENDS cpu_base

\* Common UNCHANGED for MU sync instructions that don't touch scalar state
unch_mu_sync == <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>

-----------------------------------------------------------------------------
(* MU register helpers *)

\* Read MU pointer register by code (0=MA, 1=MB, 2=MC)
MPtrValue(code) ==
    CASE code = 0 -> MA_reg [] code = 1 -> MB_reg
      [] code = 2 -> MC_reg [] OTHER -> 0

\* Write one MU register by code (0=MA..5=MK); all others UNCHANGED
SetMReg(code, val) ==
    /\ MA_reg' = IF code = 0 THEN val ELSE MA_reg
    /\ MB_reg' = IF code = 1 THEN val ELSE MB_reg
    /\ MC_reg' = IF code = 2 THEN val ELSE MC_reg
    /\ MM_reg' = IF code = 3 THEN val ELSE MM_reg
    /\ MN_reg' = IF code = 4 THEN val ELSE MN_reg
    /\ MK_reg' = IF code = 5 THEN val ELSE MK_reg

\* Shared writeback for MSET forms (target 0–5: MA/MB/MC/MM/MN/MK)
MSetWriteback(code, val, ip_inc) ==
    IF code > 5 THEN Fault(ERR_INVALID_REG)
    ELSE /\ SetMReg(code, val)
         /\ MFPSR_reg' = MFPSR_reg /\ mu_queue' = mu_queue /\ mu_fault' = mu_fault
         /\ IP' = IP + ip_inc
         /\ UNCHANGED unch_mu_sync
         /\ UNCHANGED vu_vars

-----------------------------------------------------------------------------
(* MFM byte helpers *)

MFM_fmt(mfm)      == mfm % 8           \* bits[2:0]: A/B source format code
MFM_layout(mfm)   == (mfm \div 8) % 8  \* bits[5:3]: layout flags (A_col/B_col/C_col)
MFM_reserved(mfm) == mfm \div 64       \* bits[7:6]: must be 0

\* Element size in bytes by MU format code (same as VFmtBytes)
MFmtBytes(fmt) == VFmtBytes(fmt)

\* mregs field decode (same bit positions as VRegs)
MRegs_dst(regs)  == (regs \div 64) % 4   \* bits[7:6]: C-role register
MRegs_src1(regs) == (regs \div 16) % 4   \* bits[5:4]: A-role register
MRegs_src2(regs) == (regs \div 4) % 4    \* bits[3:2]: B-role register

\* Validate MFM byte + mregs: 0 if valid, ERR_VU_FORMAT otherwise
ValidateMFM(mfm, regs) ==
    LET fmt == MFM_fmt(mfm)
        d   == MRegs_dst(regs)
        s1  == MRegs_src1(regs)
        s2  == MRegs_src2(regs)
    IN IF MFM_reserved(mfm) # 0 THEN ERR_VU_FORMAT   \* bits[7:6] non-zero
       ELSE IF fmt = 7 THEN ERR_VU_FORMAT              \* reserved format code
       ELSE IF regs % 4 # 0 THEN ERR_VU_FORMAT         \* bits[1:0] non-zero
       ELSE IF d > 2 \/ s1 > 2 \/ s2 > 2 THEN ERR_VU_FORMAT  \* only MA/MB/MC valid
       ELSE 0

-----------------------------------------------------------------------------
(* MU command tuple *)

\* Field indices into MU command tuple
MU_OP    == 1   MU_FMT    == 2   MU_LAYOUT == 3   MU_ACCUM == 4
MU_AADDR == 5   MU_BADDR  == 6   MU_CADDR  == 7
MU_M     == 8   MU_N      == 9   MU_K      == 10

\* Build MU command: snapshot state at enqueue time
\* <<op, fmt, layout, accumulate, a_addr, b_addr, c_addr, m, n, k>>
MuCommand(op, mfm, regs) ==
    <<op, MFM_fmt(mfm), MFM_layout(mfm), op = OP_MMAD,
      MPtrValue(MRegs_src1(regs)),   \* A matrix pointer
      MPtrValue(MRegs_src2(regs)),   \* B matrix pointer
      MPtrValue(MRegs_dst(regs)),    \* C matrix pointer
      MM_reg, MN_reg, MK_reg>>

\* MU fault helper: store code, flush queue
MuFaultHelper(err) ==
    /\ mu_fault' = err
    /\ mu_queue' = <<>>

-----------------------------------------------------------------------------
(* Auto-increment calculation for MMUL/MMAD *)

\* Max of two naturals (shared with cpu_ops_vector but redefined locally)
MMax(a, b) == IF a >= b THEN a ELSE b

\* Per-register increment with deduplication (same register in multiple roles → max stride)
\* roles: dc = C-role code, s1c = A-role code, s2c = B-role code
MRegIncrement(r, dc, s1c, s2c, cinc, ainc, binc) ==
    LET d == IF r = dc  THEN cinc ELSE 0
        a == IF r = s1c THEN ainc ELSE 0
        b == IF r = s2c THEN binc ELSE 0
    IN MMax(d, MMax(a, b))

\* Compute auto-increment amounts for MA / MB pointer registers.
\* MC is intentionally NOT auto-incremented so K-loop accumulation does not
\* need a re-MSET between MMAD calls.
\* Returns function: register code (0=MA,1=MB,2=MC) → increment bytes
MAutoInc(mfm, regs) ==
    LET sz   == MFmtBytes(MFM_fmt(mfm))
        m    == MM_reg
        n    == MN_reg
        k    == MK_reg
        dc   == 99                 \* sentinel: never matches any real reg code
        s1c  == MRegs_src1(regs)   \* A-role
        s2c  == MRegs_src2(regs)   \* B-role
        cinc == 0                  \* MC: no auto-increment
        ainc == m * k * sz
        binc == k * n * sz
    IN [r \in 0..2 |-> MRegIncrement(r, dc, s1c, s2c, cinc, ainc, binc)]

-----------------------------------------------------------------------------
(* Synchronous instruction handlers *)

ExecMSET_IMM16_188 == memory[IP] = OP_MSET_IMM16
    /\ LET t == Mem(IP+1) IN
       MSetWriteback(t, Mem(IP+3) * 256 + Mem(IP+2), 4)

ExecMSET_GPR_189 == memory[IP] = OP_MSET_GPR
    /\ LET t      == Mem(IP+1)
           p      == Mem(IP+2)
           single == (p \div 16) % 2 = 1
           reg    == p % 4
           val    == IF single
                     THEN RegValue(reg)
                     ELSE RegValue((p \div 4) % 4) * 256 + RegValue(reg)
       IN MSetWriteback(t, val, 3)

ExecMFSTAT_190 == memory[IP] = OP_MFSTAT
    /\ LET g == Mem(IP+1) IN
       IF g > 3 THEN Fault(ERR_INVALID_REG)
       ELSE /\ SetRegABCD(g, MFPSR_reg) /\ IP' = IP + 2
            /\ UNCHANGED <<SP,DP,Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>
            /\ UNCHANGED vu_vars
            /\ UNCHANGED <<MA_reg,MB_reg,MC_reg,MM_reg,MN_reg,MK_reg,MFPSR_reg,mu_queue,mu_fault>>

ExecMFCLR_191 == memory[IP] = OP_MFCLR
    /\ MFPSR_reg' = 0 /\ IP' = IP + 1
    /\ UNCHANGED unch_mu_sync
    /\ UNCHANGED vu_vars
    /\ UNCHANGED <<MA_reg,MB_reg,MC_reg,MM_reg,MN_reg,MK_reg,mu_queue,mu_fault>>

\* MWAIT: drain mu_queue; surface deferred fault if any
ExecMWAIT_192_fault == memory[IP] = OP_MWAIT
    /\ mu_queue = <<>>
    /\ mu_fault # 0
    /\ F' = TRUE /\ A' = mu_fault /\ state' = "FAULT"
    /\ mu_fault' = 0
    /\ UNCHANGED <<IP,SP,DP,B,C,D,Z,C_flag,memory,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>
    /\ UNCHANGED <<MA_reg,MB_reg,MC_reg,MM_reg,MN_reg,MK_reg,MFPSR_reg,mu_queue>>
    /\ UNCHANGED vu_vars

ExecMWAIT_192_ok == memory[IP] = OP_MWAIT
    /\ mu_queue = <<>>
    /\ mu_fault = 0
    /\ IP' = IP + 1
    /\ UNCHANGED unch_mu_sync /\ UNCHANGED vu_vars
    /\ UNCHANGED <<MA_reg,MB_reg,MC_reg,MM_reg,MN_reg,MK_reg,MFPSR_reg,mu_queue,mu_fault>>

ExecMWAIT_192 == ExecMWAIT_192_fault \/ ExecMWAIT_192_ok

-----------------------------------------------------------------------------
(* Asynchronous command handlers — push to mu_queue *)

\* Async: validation failed → ERR_VU_FORMAT
ExecMAsync_fault(op) ==
    /\ memory[IP] = op
    /\ ValidateMFM(Mem(IP+1), Mem(IP+2)) # 0
    /\ Fault(ValidateMFM(Mem(IP+1), Mem(IP+2)))

\* Async: M=0 or N=0 or K=0 → no-op, no auto-increment
ExecMAsync_noop(op) ==
    /\ memory[IP] = op
    /\ ValidateMFM(Mem(IP+1), Mem(IP+2)) = 0
    /\ (MM_reg = 0 \/ MN_reg = 0 \/ MK_reg = 0)
    /\ IP' = IP + InstrSize(op)
    /\ UNCHANGED unch_mu_sync /\ UNCHANGED vu_vars
    /\ UNCHANGED <<MA_reg,MB_reg,MC_reg,MM_reg,MN_reg,MK_reg,MFPSR_reg,mu_queue,mu_fault>>

\* Async: normal push to mu_queue + auto-increment at enqueue time
ExecMAsync_push(op) ==
    /\ memory[IP] = op
    /\ LET mfm  == Mem(IP+1)
           regs == Mem(IP+2)
           cmd  == MuCommand(op, mfm, regs)
           inc  == MAutoInc(mfm, regs)
       IN /\ ValidateMFM(mfm, regs) = 0
          /\ MM_reg # 0 /\ MN_reg # 0 /\ MK_reg # 0
          /\ mu_queue' = Append(mu_queue, cmd)
          /\ mu_fault' = mu_fault
          /\ MA_reg' = (MA_reg + inc[0]) % MEM_SIZE
          /\ MB_reg' = (MB_reg + inc[1]) % MEM_SIZE
          /\ MC_reg' = (MC_reg + inc[2]) % MEM_SIZE
          /\ MM_reg' = MM_reg /\ MN_reg' = MN_reg /\ MK_reg' = MK_reg
          /\ MFPSR_reg' = MFPSR_reg
          /\ IP' = IP + InstrSize(op)
          /\ UNCHANGED unch_mu_sync /\ UNCHANGED vu_vars

ExecMAsync(op) == ExecMAsync_fault(op) \/ ExecMAsync_noop(op) \/ ExecMAsync_push(op)

ExecMMUL_193 == ExecMAsync(OP_MMUL)
ExecMMAD_194 == ExecMAsync(OP_MMAD)

-----------------------------------------------------------------------------
(* MU execution step — processes one command from mu_queue *)

\* Shared: all CPU + VU + MU pointer state frozen during MuStep
MuUnchangedCPU ==
    UNCHANGED <<IP,SP,DP,A,B,C,D,Z,C_flag,F,state,step_count,cycles,
                FA_reg,FB_reg,FPCR_reg,FPSR_reg,
                MA_reg,MB_reg,MC_reg,MM_reg,MN_reg,MK_reg,
                VA_reg,VB_reg,VC_reg,VM_reg,VL_reg,VFPSR_reg,vu_queue,vu_fault>>

\* OOB check: any matrix extent exceeds 64 KB address space
MuOOB(cmd) ==
    LET sz == MFmtBytes(cmd[MU_FMT])
        m  == cmd[MU_M]
        n  == cmd[MU_N]
        k  == cmd[MU_K]
    IN (cmd[MU_AADDR] + m * k * sz > MEM_SIZE)
       \/ (cmd[MU_BADDR] + k * n * sz > MEM_SIZE)
       \/ (cmd[MU_CADDR] + m * n * 4  > MEM_SIZE)

\* MuStep: OOB → deferred fault surfaced at next MWAIT
MuStep_oob ==
    /\ mu_queue # <<>>
    /\ mu_fault = 0
    /\ MuOOB(Head(mu_queue))
    /\ MuFaultHelper(ERR_VU_OOB)
    /\ UNCHANGED <<memory, MFPSR_reg>>
    /\ MuUnchangedCPU

\* MuStep: normal execution (oracle model — verifies structure, not arithmetic)
MuStep_exec ==
    /\ mu_queue # <<>>
    /\ mu_fault = 0
    /\ ~MuOOB(Head(mu_queue))
    /\ mu_queue' = Tail(mu_queue)
    /\ mu_fault' = 0
    /\ MFPSR_reg' = MFPSR_reg
    /\ UNCHANGED memory
    /\ MuUnchangedCPU

MuStep == MuStep_oob \/ MuStep_exec

=============================================================================
