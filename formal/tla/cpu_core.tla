--------------------------- MODULE cpu_core ---------------------------
EXTENDS cpu_base, cpu_ops_mov, cpu_ops_alu, cpu_ops_jump, cpu_ops_stack, cpu_ops_mul, cpu_ops_bit, cpu_ops_fp, cpu_ops_vector

(*
   State Machine:

   IDLE ──step()──► RUNNING ──HLT──► HALTED
                       │                │
                       ├──error──► FAULT│
                       │             │  │
                       ◄──reset()────┴──┘

   States:
   - IDLE: Initial state after power-on or reset signal
   - RUNNING: Executing instructions
   - HALTED: Stopped after HLT instruction
   - FAULT: Error occurred, error code in A

   Transitions:
   - IDLE -> RUNNING: First step() call
   - RUNNING -> HALTED: HLT instruction executed
   - RUNNING -> FAULT: Error condition detected
   - HALTED -> IDLE: reset signal
   - FAULT -> IDLE: reset signal
*)

-----------------------------------------------------------------------------
(* Type Invariants *)

TypeInvariant ==
    /\ IP \in BYTE /\ SP \in BYTE /\ DP \in BYTE
    /\ A \in BYTE /\ B \in BYTE /\ C \in BYTE /\ D \in BYTE
    /\ Z \in BOOLEAN /\ C_flag \in BOOLEAN /\ F \in BOOLEAN
    /\ state \in {"IDLE", "RUNNING", "HALTED", "FAULT"}
    /\ cycles \in Nat
    /\ FA_reg \in Nat /\ FB_reg \in Nat /\ FPCR_reg \in BYTE /\ FPSR_reg \in BYTE
    /\ VA_reg \in Nat /\ VB_reg \in Nat /\ VC_reg \in Nat /\ VM_reg \in Nat
    /\ VL_reg \in Nat /\ VFPSR_reg \in BYTE /\ vu_fault \in BYTE

-----------------------------------------------------------------------------
(* State Machine Invariants *)

\* Fault flag consistency: F=TRUE iff state=FAULT
FaultConsistency == (state = "FAULT") <=> (F = TRUE)

\* Fault must have valid error code in A
FaultCodeValid == state = "FAULT" =>
    A \in {ERR_DIV_ZERO, ERR_STACK_OVERFLOW, ERR_STACK_UNDERFLOW,
           ERR_INVALID_REG, ERR_PAGE_BOUNDARY, ERR_INVALID_OPCODE,
           ERR_FP_FORMAT, ERR_VU_OOB, ERR_VU_FORMAT}

\* Non-fault states have F=FALSE
RunningNotFaulted == state = "RUNNING" => F = FALSE
HaltedNotFaulted == state = "HALTED" => F = FALSE
IdleNotFaulted == state = "IDLE" => F = FALSE

\* Stack pointer in valid range during RUNNING
StackInBounds == state = "RUNNING" => SP \in BYTE

\* DP always in valid page range
DPInPageRange == DP \in 0..(MEM_PAGES - 1)

\* Memory values always in BYTE
MemoryInByte == \A i \in DOMAIN memory: memory[i] \in BYTE

\* Step counter bounded
StepsBounded == step_count <= MAX_STEPS

\* Cycles bounded: max cost per instruction is 8 (FP32 FMADD = mem(4)+fpu_ma(4))
CyclesBounded == cycles <= MAX_STEPS * 8

\* Cycles are monotonically non-negative
CyclesNonNeg == cycles >= 0

\* Combined safety invariant
Safety == TypeInvariant /\ FaultConsistency /\ FaultCodeValid /\ DPInPageRange

-----------------------------------------------------------------------------
(* Actions *)

\* HLT - Halt execution
ExecHLT == memory[IP] = OP_HLT
    /\ state' = "HALTED" /\ IP' = IP
    /\ UNCHANGED <<SP, DP, A, B, C, D, Z, C_flag, F, memory, FA_reg, FB_reg, FPCR_reg, FPSR_reg>>
    /\ UNCHANGED vu_vars

\* Invalid opcode - FAULT
ExecInvalid == memory[IP] \notin OPCODES
    /\ Fault(ERR_INVALID_OPCODE)

\* IP overflow guard - instruction bytes or next IP would leave page 0
IPOverflowGuard ==
    /\ memory[IP] \in OPCODES
    /\ memory[IP] # OP_HLT
    /\ IP + InstrSize(memory[IP]) >= 256

\* Initialize memory with program
InitMem == [i \in 0..MEMORY_SIZE-1 |-> IF i < Len(PROGRAM) THEN PROGRAM[i+1] ELSE 0]

\* Initial state - start in IDLE
Init ==
    /\ IP = 0 /\ SP = STACK_MAX /\ DP = 0
    /\ A = 0 /\ B = 0 /\ C = 0 /\ D = 0
    /\ Z = FALSE /\ C_flag = FALSE /\ F = FALSE
    /\ memory = InitMem
    /\ state = "IDLE"
    /\ step_count = 0
    /\ cycles = 0
    /\ FA_reg = 0 /\ FB_reg = 0 /\ FPCR_reg = 0 /\ FPSR_reg = 0
    /\ VA_reg = 0 /\ VB_reg = 0 /\ VC_reg = 0 /\ VM_reg = 0
    /\ VL_reg = 0 /\ VFPSR_reg = 0 /\ vu_queue = <<>> /\ vu_fault = 0

\* First step transitions IDLE -> RUNNING
FirstStep ==
    /\ state = "IDLE"
    /\ state' = "RUNNING"
    /\ UNCHANGED <<IP, SP, DP, A, B, C, D, Z, C_flag, F, memory, step_count, cycles, FA_reg, FB_reg, FPCR_reg, FPSR_reg>>
    /\ UNCHANGED vu_vars

\* Execute one instruction (state must be RUNNING)
\* IP overflow is checked first to ensure mutual exclusion with handlers
Step ==
    /\ state = "RUNNING"
    /\ step_count < MAX_STEPS
    /\ step_count' = step_count + 1
    /\ IF IPOverflowGuard THEN Fault(ERR_PAGE_BOUNDARY)
       ELSE \/ ExecHLT
            \/ ExecMOV_1 \/ ExecMOV_2 \/ ExecMOV_3 \/ ExecMOV_4
            \/ ExecMOV_5 \/ ExecMOV_6 \/ ExecMOV_7 \/ ExecMOV_8
            \/ ExecADD_10 \/ ExecADD_11 \/ ExecADD_12 \/ ExecADD_13
            \/ ExecSUB_14 \/ ExecSUB_15 \/ ExecSUB_16 \/ ExecSUB_17
            \/ ExecINC \/ ExecDEC
            \/ ExecCMP_20 \/ ExecCMP_21 \/ ExecCMP_22 \/ ExecCMP_23
            \/ ExecJMP_30 \/ ExecJMP_31
            \/ ExecJC_32 \/ ExecJC_33 \/ ExecJNC_34 \/ ExecJNC_35
            \/ ExecJZ_36 \/ ExecJZ_37 \/ ExecJNZ_38 \/ ExecJNZ_39
            \/ ExecJA_40 \/ ExecJA_41 \/ ExecJNA_42 \/ ExecJNA_43
            \/ ExecPUSH_50 \/ ExecPUSH_51 \/ ExecPUSH_52 \/ ExecPUSH_53
            \/ ExecPOP_54
            \/ ExecCALL_55 \/ ExecCALL_56 \/ ExecRET_57
            \/ ExecMUL_60 \/ ExecMUL_61 \/ ExecMUL_62 \/ ExecMUL_63
            \/ ExecDIV_64 \/ ExecDIV_65 \/ ExecDIV_66 \/ ExecDIV_67
            \/ ExecAND_70 \/ ExecAND_71 \/ ExecAND_72 \/ ExecAND_73
            \/ ExecOR_74 \/ ExecOR_75 \/ ExecOR_76 \/ ExecOR_77
            \/ ExecXOR_78 \/ ExecXOR_79 \/ ExecXOR_80 \/ ExecXOR_81
            \/ ExecNOT_82
            \/ ExecSHL_90 \/ ExecSHL_91 \/ ExecSHL_92 \/ ExecSHL_93
            \/ ExecSHR_94 \/ ExecSHR_95 \/ ExecSHR_96 \/ ExecSHR_97
            \/ ExecFMOV_128 \/ ExecFMOV_129 \/ ExecFMOV_130 \/ ExecFMOV_131
            \/ ExecFADD_132 \/ ExecFADD_133
            \/ ExecFSUB_134 \/ ExecFSUB_135
            \/ ExecFMUL_136 \/ ExecFMUL_137
            \/ ExecFDIV_138 \/ ExecFDIV_139
            \/ ExecFCMP_140 \/ ExecFCMP_141
            \/ ExecFABS_142 \/ ExecFNEG_143 \/ ExecFSQRT_144
            \/ ExecFMOV_RR_145
            \/ ExecFCVT_146 \/ ExecFITOF_147 \/ ExecFFTOI_148
            \/ ExecFSTAT_149 \/ ExecFCFG_150 \/ ExecFSCFG_151 \/ ExecFCLR_152
            \/ ExecFADD_RR_153 \/ ExecFSUB_RR_154 \/ ExecFMUL_RR_155
            \/ ExecFDIV_RR_156 \/ ExecFCMP_RR_157
            \/ ExecFCLASS_158
            \/ ExecFMADD_A_159 \/ ExecFMADD_I_160
            \/ ExecFMOV_161 \/ ExecFMOV_162
            \/ ExecVSET_163 \/ ExecVSET_164 \/ ExecVSET_165 \/ ExecVSET_166
            \/ ExecVFSTAT_167 \/ ExecVFCLR_168 \/ ExecVWAIT_169
            \/ ExecVADD_170 \/ ExecVSUB_171 \/ ExecVMUL_172 \/ ExecVDIV_173
            \/ ExecVMAX_174 \/ ExecVMIN_175 \/ ExecVDOT_176
            \/ ExecVSQRT_177 \/ ExecVNEG_178 \/ ExecVABS_179
            \/ ExecVCMP_180 \/ ExecVSEL_181 \/ ExecVMOV_182
            \/ ExecVFILL_183
            \/ ExecInvalid
    /\ cycles' = IF state' = "RUNNING" THEN cycles + Cost(memory[IP], memory[IP+1]) ELSE cycles

\* Reset signal: from HALTED or FAULT back to IDLE
Reset ==
    /\ state \in {"HALTED", "FAULT"}
    /\ IP' = 0 /\ SP' = STACK_MAX /\ DP' = 0
    /\ A' = 0 /\ B' = 0 /\ C' = 0 /\ D' = 0
    /\ Z' = FALSE /\ C_flag' = FALSE /\ F' = FALSE
    /\ memory' = InitMem
    /\ state' = "IDLE"
    /\ step_count' = 0
    /\ cycles' = 0
    /\ FA_reg' = 0 /\ FB_reg' = 0 /\ FPCR_reg' = 0 /\ FPSR_reg' = 0
    /\ VA_reg' = 0 /\ VB_reg' = 0 /\ VC_reg' = 0 /\ VM_reg' = 0
    /\ VL_reg' = 0 /\ VFPSR_reg' = 0 /\ vu_queue' = <<>> /\ vu_fault' = 0

\* Stutter in terminal states (no Reset action taken)
Stutter == state \in {"HALTED", "FAULT"} /\ UNCHANGED vars

\* Next state relation
Next == FirstStep \/ Step \/ Reset \/ Stutter \/ VuStep

\* Specification
Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Step) /\ WF_vars(FirstStep) /\ WF_vars(VuStep)

-----------------------------------------------------------------------------
(* Temporal Properties *)

\* Eventually leaves RUNNING state
Progress == <>(state # "RUNNING")

\* Eventually terminates (reaches HALTED or FAULT)
Termination == <>(state \in {"HALTED", "FAULT"})

\* From IDLE, eventually reaches RUNNING
IdleToRunning == (state = "IDLE") ~> (state = "RUNNING")

=============================================================================
