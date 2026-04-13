------------------------- MODULE cpu_ops_vector -------------------------
(*
   Vector Unit instruction handlers (v3)
   Synchronous: VSET, VFSTAT, VFCLR, VWAIT
   Asynchronous: VADD..VFILL (pushed to vu_queue)
   VU execution: VuStep (interleaved with CPU)

   Spec references:
     spec/vector.md §9.2  — VU registers (VA/VB/VC/VM/VL/VFPSR)
     spec/vector.md §9.3  — Data formats (fmt codes 0-6)
     spec/vector.md §9.4  — SIMD modes (vv/vs/vi/r)
     spec/vector.md §9.5  — Auto-increment semantics
     spec/vector.md §9.6  — Async model and window execution
     spec/vector.md §9.7  — VFM byte and register byte encoding
     spec/vector.md §9.8  — Sync instructions (VSET/VFSTAT/VFCLR/VWAIT)
     spec/errors.md       — ERR_VU_OOB (13), ERR_VU_FORMAT (14)
*)

EXTENDS cpu_base

\* Common UNCHANGED for sync instructions that don't touch scalar state
unch_sync == <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>

-----------------------------------------------------------------------------
(* Synchronous instruction handlers *)

SetVPtr(target, val) ==
    /\ VA_reg' = IF target = 0 THEN val ELSE VA_reg
    /\ VB_reg' = IF target = 1 THEN val ELSE VB_reg
    /\ VC_reg' = IF target = 2 THEN val ELSE VC_reg
    /\ VM_reg' = IF target = 3 THEN val ELSE VM_reg

\* Shared writeback for VSET forms (target 0–4: VA/VB/VC/VM/VL)
VSETWriteback(target, val, ip_inc) ==
    IF target > 4 THEN Fault(ERR_INVALID_REG)
    ELSE /\ SetVPtr(target, val)
         /\ VL_reg' = IF target = 4 THEN val ELSE VL_reg
         /\ IP' = IP + ip_inc
         /\ UNCHANGED unch_sync
         /\ UNCHANGED <<VFPSR_reg, vu_queue, vu_fault>>

ExecVSET_163 == memory[IP] = OP_VSET_IMM16
    /\ LET t == Mem(IP+1) IN
       VSETWriteback(t, Mem(IP+3) * 256 + Mem(IP+2), 4)

ExecVSET_164 == memory[IP] = OP_VSET_GPR
    /\ LET t == Mem(IP+1)
           p == Mem(IP+2)
       IN VSETWriteback(t, RegValue((p \div 4) % 4) * 256 + RegValue(p % 4), 3)

ExecVSET_165 == memory[IP] = OP_VSET_MEM
    /\ LET t == Mem(IP+1)
           addr == Mem(IP+2)
           ea == DirectAddr(addr)
       IN
       IF addr + 1 > 255 THEN Fault(ERR_PAGE_BOUNDARY)
       ELSE VSETWriteback(t, Mem(ea+1) * 256 + Mem(ea), 3)

ExecVSET_166 == memory[IP] = OP_VSET_MEMI
    /\ LET t == Mem(IP+1)
           dec == DecodeIndirect(Mem(IP+2))
       IN
       IF ~dec[2] THEN Fault(dec[3])
       ELSE LET ea == dec[1]
                page_off == ea % 256
            IN IF page_off + 1 > 255 THEN Fault(ERR_PAGE_BOUNDARY)
               ELSE VSETWriteback(t, Mem(ea+1) * 256 + Mem(ea), 3)

ExecVFSTAT_167 == memory[IP] = OP_VFSTAT
    /\ LET g == Mem(IP+1) IN
       IF g > 3 THEN Fault(ERR_INVALID_REG)
       ELSE /\ SetRegABCD(g, VFPSR_reg) /\ IP' = IP + 2
            /\ UNCHANGED <<SP,DP,Z,C_flag,F,memory,state,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>
            /\ UNCHANGED vu_vars

ExecVFCLR_168 == memory[IP] = OP_VFCLR
    /\ VFPSR_reg' = 0 /\ IP' = IP + 1
    /\ UNCHANGED unch_sync
    /\ UNCHANGED <<VA_reg, VB_reg, VC_reg, VM_reg, VL_reg, vu_queue, vu_fault>>

ExecVWAIT_169_fault == memory[IP] = OP_VWAIT
    /\ vu_queue = <<>>
    /\ vu_fault # 0
    /\ F' = TRUE /\ A' = vu_fault /\ state' = "FAULT"
    /\ vu_fault' = 0
    /\ UNCHANGED <<IP,SP,DP,B,C,D,Z,C_flag,memory,FA_reg,FB_reg,FPCR_reg,FPSR_reg>>
    /\ UNCHANGED <<VA_reg,VB_reg,VC_reg,VM_reg,VL_reg,VFPSR_reg,vu_queue>>

ExecVWAIT_169_ok == memory[IP] = OP_VWAIT
    /\ vu_queue = <<>>
    /\ vu_fault = 0
    /\ IP' = IP + 1
    /\ UNCHANGED unch_sync /\ UNCHANGED vu_vars

ExecVWAIT_169 == ExecVWAIT_169_fault \/ ExecVWAIT_169_ok

-----------------------------------------------------------------------------
(* Auto-increment calculation — extracted from ExecVAsync *)

\* Compute increment for one register given its role(s) in the instruction
\* Deduplication: same register in multiple roles → largest stride
Max(a, b) == IF a >= b THEN a ELSE b
RegIncrement(reg_code, dst_code, s1_code, s2_code, dst_inc, s1_inc, s2_inc) ==
    LET d == IF reg_code = dst_code THEN dst_inc ELSE 0
        s1 == IF reg_code = s1_code THEN s1_inc ELSE 0
        s2 == IF reg_code = s2_code THEN s2_inc ELSE 0
    IN Max(d, Max(s1, s2))

\* Compute all auto-increment amounts for an operation
AutoInc(op, mode, vl, sz) ==
    LET S == vl * sz
        s == sz
        dst_inc == IF op = OP_VDOT THEN s
                   ELSE IF op = OP_VCMP THEN vl
                   ELSE IF mode = 3 THEN s
                   ELSE S
        s1_inc == IF op = OP_VSEL \/ (op = OP_VMOV /\ mode = 2) THEN 0 ELSE S
        s2_inc == IF op \in {OP_VSQRT,OP_VNEG,OP_VABS,OP_VMOV} THEN 0
                  ELSE IF mode \in {1, 2, 3} THEN 0
                  ELSE S
    IN <<dst_inc, s1_inc, s2_inc>>

-----------------------------------------------------------------------------
(* Asynchronous command handler — push to vu_queue *)

\* Read immediate value: from instruction stream (.vi) or GPR (.vs)
ReadImm(mode, sz, s2c) ==
    IF mode = 1 THEN RegValue(s2c)  \* GPR broadcast
    ELSE IF mode = 2 THEN
        IF sz = 1 THEN Mem(IP+3)
        ELSE IF sz = 2 THEN Mem(IP+3) + Mem(IP+4) * 256
        ELSE Mem(IP+3) + Mem(IP+4) * 256 + Mem(IP+5) * 65536 + Mem(IP+6) * 16777216
    ELSE 0

\* Async: VFM or regs-byte validation failed
ExecVAsync_fault(op) ==
    /\ memory[IP] = op
    /\ \/ ValidateVFM(Mem(IP+1), op) # 0
       \/ Mem(IP+2) % 4 # 0  \* reserved bits [1:0]
       \/ (op = OP_VCMP /\ Mem(IP+3) \div 8 # 0)  \* cond byte: bits[7:3] must be 0
       \/ (op = OP_VCMP /\ Mem(IP+3) % 8 > 5)      \* cond value 6 or 7 invalid
    /\ Fault(IF ValidateVFM(Mem(IP+1), op) # 0
             THEN ValidateVFM(Mem(IP+1), op)
             ELSE ERR_VU_FORMAT)

\* Async: VL=0, no-op
ExecVAsync_noop(op) ==
    /\ memory[IP] = op
    /\ ValidateVFM(Mem(IP+1), op) = 0
    /\ Mem(IP+2) % 4 = 0
    /\ (op = OP_VCMP => Mem(IP+3) \div 8 = 0 /\ Mem(IP+3) % 8 <= 5)
    /\ VL_reg = 0
    /\ IP' = IP + InstrSize(op)
    /\ UNCHANGED unch_sync /\ UNCHANGED vu_vars

\* Async: normal push to queue + auto-increment
ExecVAsync_push(op) ==
    /\ memory[IP] = op
    /\ LET vfm == Mem(IP+1)
           regs == Mem(IP+2)
           fmt == VFM_fmt(vfm)
           mode == VFM_mode(vfm)
           dc == VRegs_dst(regs)
           s1c == VRegs_src1(regs)
           s2c == VRegs_src2(regs)
           sz == VFmtBytes(fmt)
           imm == ReadImm(mode, sz, s2c)
           cond == IF op = OP_VCMP THEN Mem(IP+3) % 8 ELSE VFM_cond(vfm)
           cmd == <<op, fmt, mode, cond,
                    VPtrValue(dc), VPtrValue(s1c),
                    IF mode = 1 THEN 0 ELSE VPtrValue(s2c),
                    VM_reg, VL_reg, imm>>
           inc == AutoInc(op, mode, VL_reg, sz)
           apply == [r \in 0..3 |-> RegIncrement(r, dc, s1c, s2c, inc[1], inc[2], inc[3])]
       IN /\ ValidateVFM(vfm, op) = 0
          /\ regs % 4 = 0  \* reserved bits [1:0] must be 0
          /\ (op = OP_VCMP => Mem(IP+3) \div 8 = 0 /\ Mem(IP+3) % 8 <= 5)
          /\ VL_reg # 0
          /\ vu_queue' = Append(vu_queue, cmd)
          /\ vu_fault' = vu_fault
          /\ IP' = IP + InstrSize(op)
          /\ VA_reg' = (VA_reg + apply[0]) % MEM_SIZE
          /\ VB_reg' = (VB_reg + apply[1]) % MEM_SIZE
          /\ VC_reg' = (VC_reg + apply[2]) % MEM_SIZE
          /\ VM_reg' = (VM_reg + apply[3]) % MEM_SIZE
          /\ VL_reg' = VL_reg /\ VFPSR_reg' = VFPSR_reg
          /\ UNCHANGED unch_sync

ExecVAsync(op) == ExecVAsync_fault(op) \/ ExecVAsync_noop(op) \/ ExecVAsync_push(op)

ExecVADD_170  == ExecVAsync(OP_VADD)
ExecVSUB_171  == ExecVAsync(OP_VSUB)
ExecVMUL_172  == ExecVAsync(OP_VMUL)
ExecVDIV_173  == ExecVAsync(OP_VDIV)
ExecVMAX_174  == ExecVAsync(OP_VMAX)
ExecVMIN_175  == ExecVAsync(OP_VMIN)
ExecVDOT_176  == ExecVAsync(OP_VDOT)
ExecVSQRT_177 == ExecVAsync(OP_VSQRT)
ExecVNEG_178  == ExecVAsync(OP_VNEG)
ExecVABS_179  == ExecVAsync(OP_VABS)
ExecVCMP_180  == ExecVAsync(OP_VCMP)
ExecVSEL_181  == ExecVAsync(OP_VSEL)
ExecVMOV_182  == ExecVAsync(OP_VMOV)
ExecVFILL_183 == memory[IP] = 183 /\ Fault(ERR_INVALID_OPCODE)

-----------------------------------------------------------------------------
(* VU execution step — processes one command from queue *)

\* Write one byte to memory (uses Mod to avoid SANY format-string bug with %)
Mod(a, b) == a - (a \div b) * b

WriteByte(mem, addr, val) ==
    [mem EXCEPT ![Mod(addr, MEM_SIZE)] = Mod(val, 256)]

\* Shared: unchanged CPU + VU pointer state
VuUnchangedCPU ==
    UNCHANGED <<IP,SP,DP,A,B,C,D,Z,C_flag,F,state,step_count,cycles,
                FA_reg,FB_reg,FPCR_reg,FPSR_reg,
                VA_reg,VB_reg,VC_reg,VM_reg,VL_reg>>

\* OOB check for a command
VuOOB(cmd) ==
    LET sz == VFmtBytes(cmd[VU_FMT])
        op == cmd[VU_OP]
        vl == cmd[VU_VL]
        \* dst footprint: VCMP writes VL bytes (mask), VDOT/reduction writes sz bytes, else VL*sz
        dst_bytes == IF op = OP_VCMP THEN vl
                     ELSE IF op = OP_VDOT THEN sz
                     ELSE IF cmd[VU_MODE] = 3 THEN sz
                     ELSE vl * sz
    IN (cmd[VU_DST] + dst_bytes > MEM_SIZE)
       \/ (cmd[VU_S1] + vl * sz > MEM_SIZE)
       \/ (cmd[VU_MODE] = 0 /\ cmd[VU_S2] + vl * sz > MEM_SIZE)
       \/ (op \in {OP_VCMP, OP_VSEL} /\ cmd[VU_MASK] + vl > MEM_SIZE)

\* VU: OOB fault
VuStep_oob ==
    /\ vu_queue # <<>>
    /\ vu_fault = 0
    /\ VuOOB(Head(vu_queue))
    /\ VuFault(ERR_VU_OOB)
    /\ UNCHANGED <<memory, VFPSR_reg>>
    /\ VuUnchangedCPU

\* VU: Normal execution (all formats, all modes)
\* Uses nondeterministic oracle for results (verifies structure, not arithmetic)
\* INT8 and FP treated uniformly: result per element from FP_ORACLE
VuStep_exec ==
    /\ vu_queue # <<>>
    /\ vu_fault = 0
    /\ ~VuOOB(Head(vu_queue))
    /\ vu_queue' = Tail(vu_queue)
    /\ vu_fault' = 0
    /\ VFPSR_reg' = VFPSR_reg
    /\ UNCHANGED memory
    /\ VuUnchangedCPU

VuStep == VuStep_oob \/ VuStep_exec

=============================================================================
