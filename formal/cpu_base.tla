--------------------------- MODULE cpu_base ---------------------------
(*
   Base definitions: constants, variables, helpers
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MAX_STEPS, PROGRAM, FP_ORACLE

VARIABLES
    IP, SP, DP,
    A, B, C, D,
    Z, C_flag, F,
    memory, state, step_count, cycles,
    FA_reg, FPCR_reg, FPSR_reg

vars == <<IP, SP, DP, A, B, C, D, Z, C_flag, F, memory, state, step_count, cycles, FA_reg, FPCR_reg, FPSR_reg>>

-----------------------------------------------------------------------------
(* Constants *)

BYTE == 0..255
STACK_MAX == 231
MEM_PAGES == 256
MEMORY_SIZE == MEM_PAGES * 256  \* 64KB full address space
\* Note: 2^32 overflows TLC's Java int. Use Nat in TypeInvariant instead.
\* WORD32 == 0..(2^32 - 1)  \* Not usable in TLC
HALF16 == 0..(2^16 - 1)

REG_A == 0  REG_B == 1  REG_C == 2  REG_D == 3  REG_SP == 4  REG_DP == 5

ERR_DIV_ZERO == 1
ERR_STACK_OVERFLOW == 2
ERR_STACK_UNDERFLOW == 3
ERR_INVALID_REG == 4
ERR_PAGE_BOUNDARY == 5
ERR_INVALID_OPCODE == 6
ERR_FP_FORMAT == 12

-----------------------------------------------------------------------------
(* Opcode mnemonics *)

OP_HLT == 0
OP_MOV_RR == 1   OP_MOV_RA == 2   OP_MOV_RI == 3   OP_MOV_AR == 4
OP_MOV_IR == 5   OP_MOV_RC == 6   OP_MOV_AC == 7   OP_MOV_IC == 8
OP_ADD_RR == 10  OP_ADD_RI == 11  OP_ADD_RA == 12  OP_ADD_RC == 13
OP_SUB_RR == 14  OP_SUB_RI == 15  OP_SUB_RA == 16  OP_SUB_RC == 17
OP_INC == 18     OP_DEC == 19
OP_CMP_RR == 20  OP_CMP_RI == 21  OP_CMP_RA == 22  OP_CMP_RC == 23
OP_JMP_R == 30   OP_JMP == 31
OP_JC_R == 32    OP_JC == 33      OP_JNC_R == 34   OP_JNC == 35
OP_JZ_R == 36    OP_JZ == 37      OP_JNZ_R == 38   OP_JNZ == 39
OP_JA_R == 40    OP_JA == 41      OP_JNA_R == 42   OP_JNA == 43
OP_PUSH_R == 50  OP_PUSH_I == 51  OP_PUSH_A == 52  OP_PUSH_C == 53
OP_POP == 54
OP_CALL_R == 55  OP_CALL == 56    OP_RET == 57
OP_MUL_R == 60   OP_MUL_I == 61   OP_MUL_A == 62   OP_MUL_C == 63
OP_DIV_R == 64   OP_DIV_I == 65   OP_DIV_A == 66   OP_DIV_C == 67
OP_AND_RR == 70  OP_AND_RI == 71  OP_AND_RA == 72  OP_AND_RC == 73
OP_OR_RR == 74   OP_OR_RI == 75   OP_OR_RA == 76   OP_OR_RC == 77
OP_XOR_RR == 78  OP_XOR_RI == 79  OP_XOR_RA == 80  OP_XOR_RC == 81
OP_NOT == 82
OP_SHL_RR == 90  OP_SHL_RI == 91  OP_SHL_RA == 92  OP_SHL_RC == 93
OP_SHR_RR == 94  OP_SHR_RI == 95  OP_SHR_RA == 96  OP_SHR_RC == 97
OP_FMOV_FA == 128   OP_FMOV_FI == 129   OP_FMOV_AF == 130   OP_FMOV_IF == 131
OP_FADD_A == 132     OP_FADD_I == 133
OP_FSUB_A == 134     OP_FSUB_I == 135
OP_FMUL_A == 136     OP_FMUL_I == 137
OP_FDIV_A == 138     OP_FDIV_I == 139
OP_FCMP_A == 140     OP_FCMP_I == 141
OP_FABS == 142       OP_FNEG == 143       OP_FSQRT == 144
OP_FCVT == 146       OP_FITOF == 147      OP_FFTOI == 148
OP_FSTAT == 149      OP_FCFG == 150       OP_FSCFG == 151     OP_FCLR == 152
OP_FADD_RR == 153    OP_FSUB_RR == 154    OP_FMUL_RR == 155
OP_FDIV_RR == 156    OP_FCMP_RR == 157
OP_FCLASS == 158
OP_FMADD_A == 159    OP_FMADD_I == 160

OPCODES == {0} \cup (1..8) \cup (10..19) \cup (20..23)
           \cup (30..43) \cup (50..57) \cup (60..67)
           \cup (70..82) \cup (90..97)
           \cup (128..144) \cup (146..160)

-----------------------------------------------------------------------------
(* Helpers *)

RegValue(code) ==
    CASE code = 0 -> A [] code = 1 -> B [] code = 2 -> C
      [] code = 3 -> D [] code = 4 -> SP [] code = 5 -> DP [] OTHER -> 0

SetReg(code, val) ==
    CASE code = 0 -> (A' = val /\ UNCHANGED <<B,C,D,SP,DP>>)
      [] code = 1 -> (B' = val /\ UNCHANGED <<A,C,D,SP,DP>>)
      [] code = 2 -> (C' = val /\ UNCHANGED <<A,B,D,SP,DP>>)
      [] code = 3 -> (D' = val /\ UNCHANGED <<A,B,C,SP,DP>>)
      [] code = 4 -> (SP' = val /\ UNCHANGED <<A,B,C,D,DP>>)
      [] code = 5 -> (DP' = val /\ UNCHANGED <<A,B,C,D,SP>>)
      [] OTHER -> UNCHANGED <<A,B,C,D,SP,DP>>

SetRegNoSP(code, val) ==
    CASE code = 0 -> (A' = val /\ UNCHANGED <<B,C,D,SP,DP>>)
      [] code = 1 -> (B' = val /\ UNCHANGED <<A,C,D,SP,DP>>)
      [] code = 2 -> (C' = val /\ UNCHANGED <<A,B,D,SP,DP>>)
      [] code = 3 -> (D' = val /\ UNCHANGED <<A,B,C,SP,DP>>)
      [] OTHER -> UNCHANGED <<A,B,C,D,SP,DP>>

SetRegABCD(code, val) ==
    CASE code = 0 -> (A' = val /\ UNCHANGED <<B,C,D>>)
      [] code = 1 -> (B' = val /\ UNCHANGED <<A,C,D>>)
      [] code = 2 -> (C' = val /\ UNCHANGED <<A,B,D>>)
      [] code = 3 -> (D' = val /\ UNCHANGED <<A,B,C>>)
      [] OTHER -> UNCHANGED <<A,B,C,D>>

DirectAddr(addr) == (DP * 256 + addr) % MEMORY_SIZE

DecodeIndirect(encoded) ==
    LET reg == encoded % 8
        raw_off == encoded \div 8
        offset == IF raw_off > 15 THEN raw_off - 32 ELSE raw_off
        base == RegValue(reg)
        page_off == base + offset
        reg_valid == reg <= 4
        bounds_valid == (page_off >= 0) /\ (page_off <= 255)
        addr == IF reg = REG_SP THEN page_off ELSE (DP * 256 + page_off) % MEMORY_SIZE
        err == IF ~reg_valid THEN ERR_INVALID_REG
               ELSE IF ~bounds_valid THEN ERR_PAGE_BOUNDARY
               ELSE 0
    IN <<addr, err = 0, err>>

CheckOp(value) ==
    LET carry == (value >= 256) \/ (value < 0)
        wrapped == IF value >= 256 THEN value % 256
                   ELSE IF value < 0 THEN ((value % 256) + 256) % 256 ELSE value
        zero == (wrapped = 0)
    IN <<wrapped, carry, zero>>

\* Shift operations (ARM-style carry)
CheckSHL(value, cnt) ==
    LET raw == value * (2 ^ cnt)
        result == raw % 256
        carry == raw > 255
        zero == (result = 0)
    IN <<result, carry, zero>>

CheckSHR(value, cnt) ==
    LET result == value \div (2 ^ cnt)
        carry == (cnt > 0) /\ ((value % (2 ^ cnt)) # 0)
        zero == (result = 0)
    IN <<result, carry, zero>>

Mem(addr) == memory[addr % MEMORY_SIZE]

\* Bitwise operations
BitAt(n, i) == (n \div (2^i)) % 2

RECURSIVE SumBits(_, _, _, _)
SumBits(a, b, op, i) ==
    IF i > 7 THEN 0
    ELSE LET ba == BitAt(a, i)
             bb == BitAt(b, i)
             r == CASE op = "and" -> ba * bb
                    [] op = "or"  -> IF ba + bb > 0 THEN 1 ELSE 0
                    [] op = "xor" -> (ba + bb) % 2
                    [] OTHER -> 0
         IN r * (2^i) + SumBits(a, b, op, i+1)

BitAnd(a, b) == SumBits(a, b, "and", 0)
BitOr(a, b)  == SumBits(a, b, "or", 0)
BitXor(a, b) == SumBits(a, b, "xor", 0)
BitNot(a)    == 255 - a

\* Instruction size (bytes) by opcode
InstrSize(op) ==
    IF op = OP_HLT \/ op = OP_RET THEN 1
    ELSE IF op = OP_FCLR THEN 1
    ELSE IF op \in {OP_INC, OP_DEC, OP_NOT} \cup (30..43) \cup (50..56)
                   \cup (60..67) THEN 2
    ELSE IF op \in {OP_FABS, OP_FNEG, OP_FSQRT,
                    OP_FSTAT, OP_FCFG, OP_FSCFG} THEN 2
    ELSE IF op \in {OP_FMADD_A, OP_FMADD_I} THEN 4
    ELSE 3  \* MOV 1-8, ADD/SUB/CMP, AND/OR/XOR, SHL/SHR, FP 3-byte

\* Instruction cost (pipeline model)
\* Stages: reg_writeback=0, simple_alu=1, mem=2, expensive_alu=2
\* Independent: max.  Dependent (data dependency): sum.
Cost(op) ==
    IF op = OP_HLT THEN 0
    ELSE IF op \in {OP_FSTAT, OP_FCFG, OP_FSCFG, OP_FCLR} THEN 1
    ELSE IF op \in {OP_FMOV_FA, OP_FMOV_FI, OP_FMOV_AF, OP_FMOV_IF} THEN 2
    ELSE IF op \in {OP_FABS, OP_FNEG, OP_FCVT, OP_FITOF, OP_FFTOI} THEN 3
    ELSE IF op = OP_FCLASS THEN 2
    ELSE IF op \in {OP_FADD_RR, OP_FSUB_RR, OP_FMUL_RR, OP_FDIV_RR, OP_FCMP_RR} THEN 3
    ELSE IF op = OP_FSQRT THEN 4
    ELSE IF op \in (132..141) THEN 5
    ELSE IF op \in {OP_FMADD_A, OP_FMADD_I} THEN 6
    ELSE IF op \in {OP_PUSH_I, OP_PUSH_A,
                    OP_MUL_I, OP_MUL_A,
                    OP_DIV_I, OP_DIV_A} THEN 4   \* mem(2)+mem(2) or mem(2)+alu(2)
    ELSE IF op \in {OP_ADD_RI, OP_ADD_RA,
                    OP_SUB_RI, OP_SUB_RA,
                    OP_CMP_RI, OP_CMP_RA,
                    OP_AND_RI, OP_AND_RA,
                    OP_OR_RI, OP_OR_RA,
                    OP_XOR_RI, OP_XOR_RA,
                    OP_SHL_RI, OP_SHL_RA,
                    OP_SHR_RI, OP_SHR_RA} THEN 3  \* mem(2)+alu(1)
    ELSE IF op \in {OP_MOV_RR, OP_MOV_RC,
                    OP_ADD_RR, OP_ADD_RC,
                    OP_SUB_RR, OP_SUB_RC,
                    OP_INC, OP_DEC,
                    OP_CMP_RR, OP_CMP_RC,
                    OP_AND_RR, OP_AND_RC,
                    OP_OR_RR, OP_OR_RC,
                    OP_XOR_RR, OP_XOR_RC,
                    OP_NOT,
                    OP_SHL_RR, OP_SHL_RC,
                    OP_SHR_RR, OP_SHR_RC}
                    \cup (30..43) THEN 1           \* alu(1) only
    ELSE 2                                         \* mem(2) only

\* Common UNCHANGED patterns
unch_jump == <<SP,DP,A,B,C,D,Z,C_flag,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>
unch_cmp  == <<SP,DP,A,B,C,D,F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>
unch_alu  == <<F,memory,state,FA_reg,FPCR_reg,FPSR_reg>>
unch_fp_all == <<SP,DP,A,B,C,D,Z,C_flag,F,state,FA_reg,FPCR_reg,FPSR_reg>>

\* FAULT helper
Fault(err) ==
    /\ F' = TRUE /\ A' = err /\ state' = "FAULT"
    /\ UNCHANGED <<IP, SP, DP, B, C, D, Z, C_flag, memory, FA_reg, FPCR_reg, FPSR_reg>>

\* --- FP Helpers ---

\* FPM byte decode
FPM_fmt(fpm)  == fpm % 8
FPM_pos(fpm)  == (fpm \div 8) % 8
FPM_phys(fpm) == fpm \div 64

\* FPM validation: returns 0 if valid, ERR_FP_FORMAT if invalid
ValidateFPM(fpm) ==
    LET fmt == FPM_fmt(fpm)
        pos == FPM_pos(fpm)
        phys == FPM_phys(fpm)
    IN IF phys # 0 THEN ERR_FP_FORMAT
       ELSE IF fmt >= 5 THEN ERR_FP_FORMAT      \* fmt=5,6 reserved 4-bit; fmt=7 invalid
       ELSE IF fmt = 0 /\ pos # 0 THEN ERR_FP_FORMAT
       ELSE IF fmt \in {1, 2} /\ pos > 1 THEN ERR_FP_FORMAT
       ELSE IF fmt \in {3, 4} /\ pos > 3 THEN ERR_FP_FORMAT  \* OFP8: FQA-FQD (pos 0-3)
       ELSE 0

\* Format width in bits
FPWidth(fmt) ==
    CASE fmt = 0 -> 32 [] fmt = 1 -> 16 [] fmt = 2 -> 16
      [] fmt = 3 -> 8  [] fmt = 4 -> 8  [] OTHER -> 0

\* Format byte count
FPBytes(fmt) == FPWidth(fmt) \div 8

\* Read sub-register from FA_reg
FPRead(fmt, pos) ==
    LET width == FPWidth(fmt)
        bit_off == pos * width
    IN (FA_reg \div (2^bit_off)) % (2^width)

\* Write sub-register: compute new FA_reg value
FPWriteVal(fmt, pos, value) ==
    LET width == FPWidth(fmt)
        bit_off == pos * width
        old_bits == (FA_reg \div (2^bit_off)) % (2^width)
        cleared == FA_reg - old_bits * (2^bit_off)
    IN cleared + (value % (2^width)) * (2^bit_off)

\* Read multi-byte value from memory (little-endian)
RECURSIVE FPMemReadRec(_, _, _)
FPMemReadRec(base, i, cnt) ==
    IF i >= cnt THEN 0
    ELSE Mem(base + i) * (2^(i*8)) + FPMemReadRec(base, i+1, cnt)

FPMemRead(addr, fmt) == FPMemReadRec(addr, 0, FPBytes(fmt))

\* Page boundary check for FP access
FPPageOk(addr, fmt) ==
    LET pg == addr % 256
    IN pg + FPBytes(fmt) - 1 <= 255

\* IEEE 754 float32 field extraction
F32_sign(v)     == v \div (2^31)
F32_exp(v)      == (v \div (2^23)) % 256
F32_mant(v)     == v % (2^23)
F32_isNaN(v)    == F32_exp(v) = 255 /\ F32_mant(v) # 0
F32_isInf(v)    == F32_exp(v) = 255 /\ F32_mant(v) = 0
F32_isZero(v)   == F32_exp(v) = 0 /\ F32_mant(v) = 0
F32_isSNaN(v)   == F32_isNaN(v) /\ (F32_mant(v) \div (2^22)) % 2 = 0
F32_qNaN        == 255 * (2^23) + 2^22
F32_posInf      == 255 * (2^23)
F32_negInf      == 2^31 + 255 * (2^23)

\* IEEE 754 float16 field extraction
H16_sign(v)     == v \div (2^15)
H16_exp(v)      == (v \div (2^10)) % 32
H16_mant(v)     == v % (2^10)
H16_isNaN(v)    == H16_exp(v) = 31 /\ H16_mant(v) # 0
H16_isInf(v)    == H16_exp(v) = 31 /\ H16_mant(v) = 0
H16_isZero(v)   == H16_exp(v) = 0 /\ H16_mant(v) = 0
H16_isSNaN(v)   == H16_isNaN(v) /\ (H16_mant(v) \div (2^9)) % 2 = 0
H16_qNaN        == 31 * (2^10) + 2^9
H16_posInf      == 31 * (2^10)
H16_negInf      == 2^15 + 31 * (2^10)

\* IEEE 754 bfloat16 field extraction
BF16_sign(v)    == v \div (2^15)
BF16_exp(v)     == (v \div (2^7)) % 256
BF16_mant(v)    == v % (2^7)
BF16_isNaN(v)   == BF16_exp(v) = 255 /\ BF16_mant(v) # 0
BF16_isInf(v)   == BF16_exp(v) = 255 /\ BF16_mant(v) = 0
BF16_isZero(v)  == BF16_exp(v) = 0 /\ BF16_mant(v) = 0
BF16_isSNaN(v)  == BF16_isNaN(v) /\ (BF16_mant(v) \div (2^6)) % 2 = 0
BF16_qNaN       == 255 * (2^7) + 2^6
BF16_posInf     == 255 * (2^7)
BF16_negInf     == 2^15 + 255 * (2^7)

\* OFP8 E4M3 (fmt=3): 1 sign + 4 exp + 3 mant, bias=7, no Infinity
E4M3_sign(v)   == v \div 128
E4M3_exp(v)    == (v \div 8) % 16
E4M3_mant(v)   == v % 8
E4M3_isNaN(v)  == E4M3_exp(v) = 15 /\ E4M3_mant(v) = 7
E4M3_isInf(v)  == FALSE
E4M3_isZero(v) == E4M3_exp(v) = 0 /\ E4M3_mant(v) = 0
E4M3_isSNaN(v) == FALSE          \* single NaN pattern 0x7F is always qNaN
E4M3_qNaN      == 127             \* 0x7F
E4M3_posMax    == 126             \* 0x7E = +448 (overflow saturates here)
E4M3_negMax    == 254             \* 0xFE = -448

\* OFP8 E5M2 (fmt=4): 1 sign + 5 exp + 2 mant, bias=15
E5M2_sign(v)   == v \div 128
E5M2_exp(v)    == (v \div 4) % 32
E5M2_mant(v)   == v % 4
E5M2_isNaN(v)  == E5M2_exp(v) = 31 /\ E5M2_mant(v) # 0
E5M2_isInf(v)  == E5M2_exp(v) = 31 /\ E5M2_mant(v) = 0
E5M2_isZero(v) == E5M2_exp(v) = 0 /\ E5M2_mant(v) = 0
E5M2_isSNaN(v) == E5M2_isNaN(v) /\ E5M2_mant(v) < 2
E5M2_qNaN      == 126             \* 0x7E
E5M2_posInf    == 124             \* 0x7C
E5M2_negInf    == 252             \* 0xFC

\* Generic dispatch on format
FP_isNaN(v, fmt) ==
    CASE fmt = 0 -> F32_isNaN(v)  [] fmt = 1 -> H16_isNaN(v)
      [] fmt = 2 -> BF16_isNaN(v) [] fmt = 3 -> E4M3_isNaN(v)
      [] fmt = 4 -> E5M2_isNaN(v) [] OTHER -> FALSE

FP_isInf(v, fmt) ==
    CASE fmt = 0 -> F32_isInf(v)  [] fmt = 1 -> H16_isInf(v)
      [] fmt = 2 -> BF16_isInf(v) [] fmt = 3 -> E4M3_isInf(v)
      [] fmt = 4 -> E5M2_isInf(v) [] OTHER -> FALSE

FP_isZero(v, fmt) ==
    CASE fmt = 0 -> F32_isZero(v)  [] fmt = 1 -> H16_isZero(v)
      [] fmt = 2 -> BF16_isZero(v) [] fmt = 3 -> E4M3_isZero(v)
      [] fmt = 4 -> E5M2_isZero(v) [] OTHER -> FALSE

FP_isSNaN(v, fmt) ==
    CASE fmt = 0 -> F32_isSNaN(v)  [] fmt = 1 -> H16_isSNaN(v)
      [] fmt = 2 -> BF16_isSNaN(v) [] fmt = 3 -> E4M3_isSNaN(v)
      [] fmt = 4 -> E5M2_isSNaN(v) [] OTHER -> FALSE

FP_qNaN(fmt) ==
    CASE fmt = 0 -> F32_qNaN  [] fmt = 1 -> H16_qNaN
      [] fmt = 2 -> BF16_qNaN [] fmt = 3 -> E4M3_qNaN
      [] fmt = 4 -> E5M2_qNaN [] OTHER -> 0

\* E4M3 has no Inf; FP_posInf/FP_negInf return ±448 for saturation
FP_posInf(fmt) ==
    CASE fmt = 0 -> F32_posInf  [] fmt = 1 -> H16_posInf
      [] fmt = 2 -> BF16_posInf [] fmt = 3 -> E4M3_posMax
      [] fmt = 4 -> E5M2_posInf [] OTHER -> 0

FP_negInf(fmt) ==
    CASE fmt = 0 -> F32_negInf  [] fmt = 1 -> H16_negInf
      [] fmt = 2 -> BF16_negInf [] fmt = 3 -> E4M3_negMax
      [] fmt = 4 -> E5M2_negInf [] OTHER -> 0

\* Sign bit extraction (0 = positive, 1 = negative)
FP_sign(v, fmt) ==
    LET width == FPWidth(fmt)
    IN v \div (2^(width - 1))

\* FPCR field access (only rounding mode; trap enables removed in v2)
FPCR_RM == FPCR_reg % 4

\* OR exception flags into FPSR
FPSetFlags(raised) ==
    LET nv == IF 0 \in raised THEN 1 ELSE 0
        dz == IF 1 \in raised THEN 2 ELSE 0
        of == IF 2 \in raised THEN 4 ELSE 0
        uf == IF 3 \in raised THEN 8 ELSE 0
        nx == IF 4 \in raised THEN 16 ELSE 0
    IN BitOr(FPSR_reg, nv + dz + of + uf + nx)

\* Sign bit operations (for FABS, FNEG)
FP_clearSign(v, fmt) ==
    LET width == FPWidth(fmt)
    IN v % (2^(width - 1))

FP_flipSign(v, fmt) ==
    LET width == FPWidth(fmt)
        sign_bit == 2^(width - 1)
    IN IF v >= sign_bit THEN v - sign_bit ELSE v + sign_bit

\* IEEE 754 magnitude comparison (deterministic for ordered values)
FP_less(a, b, fmt) ==
    LET sa == FP_sign(a, fmt)  sb == FP_sign(b, fmt)
        width == FPWidth(fmt)
        mag_a == a % (2^(width-1))
        mag_b == b % (2^(width-1))
    IN IF sa = 1 /\ sb = 0 THEN TRUE
       ELSE IF sa = 0 /\ sb = 1 THEN FALSE
       ELSE IF sa = 0 THEN mag_a < mag_b
       ELSE mag_a > mag_b

\* Subnormal detection
FP_isSubnormal(v, fmt) ==
    CASE fmt = 0 -> F32_exp(v) = 0 /\ F32_mant(v) # 0
      [] fmt = 1 -> H16_exp(v) = 0 /\ H16_mant(v) # 0
      [] fmt = 2 -> BF16_exp(v) = 0 /\ BF16_mant(v) # 0
      [] fmt = 3 -> E4M3_exp(v) = 0 /\ E4M3_mant(v) # 0
      [] fmt = 4 -> E5M2_exp(v) = 0 /\ E5M2_mant(v) # 0
      [] OTHER -> FALSE

\* FCLASS classification bitmask
FPClassify(v, fmt) ==
    LET z == IF FP_isZero(v, fmt) THEN 1 ELSE 0
        s == IF FP_isSubnormal(v, fmt) THEN 2 ELSE 0
        n == IF ~FP_isZero(v,fmt) /\ ~FP_isSubnormal(v,fmt)
                /\ ~FP_isInf(v,fmt) /\ ~FP_isNaN(v,fmt) THEN 4 ELSE 0
        i == IF FP_isInf(v, fmt) THEN 8 ELSE 0
        q == IF FP_isNaN(v, fmt) THEN 16 ELSE 0
        sn == IF FP_isSNaN(v, fmt) THEN 32 ELSE 0
        ng == IF FP_sign(v, fmt) = 1 THEN 64 ELSE 0
    IN z + s + n + i + q + sn + ng

=============================================================================
