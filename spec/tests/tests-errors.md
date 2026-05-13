# Error Code & Fault State Machine Tests

> Architecture v3 | Part of [Technical Specification](../spec.md) | See also: [Error Codes](../errors.md), [CPU Tests](tests-cpu.md), [FP Tests](tests-fp.md), [VU Tests](tests-vu.md), [MU Tests](tests-mu.md)

## Scope

Tests in this file verify:
1. **Correct error code value** (A register) for each `ERR_*` condition.
2. **Fault state machine** — `F=true`, IP frozen, Z/C preserved, A overwritten.
3. **Cross-cutting fault behavior** — conditions not covered in domain-specific test files.

Tests for fault *triggering conditions* live in domain files:
- CPU faults (ERR_DIV_ZERO, ERR_STACK_*, ERR_INVALID_REG, ERR_PAGE_BOUNDARY, ERR_INVALID_OPCODE): [tests-cpu.md §6.20](tests-cpu.md)
- FP faults (ERR_FP_FORMAT): [tests-fp.md]
- VU faults (ERR_VU_FORMAT, ERR_VU_OOB): [tests-vu.md §10.14]

This file does **not** duplicate those; it verifies code correctness and fault-machine invariants.

---

## Methodology

Each test assembles source, runs to FAULT or HLT, then verifies:

| Target | Description |
|--------|-------------|
| `F` | Fault flag (`true` = FAULT) |
| `A` | Error code (only meaningful when `F=true`) |
| `IP` | Instruction pointer (frozen on FAULT) |
| `Z`, `C` | Must equal pre-fault values |

---

## E.1 Error Code Values

Verify each `ERR_*` produces exactly the specified code in `A`.

| # | Trigger | Verify | ERR_ name |
|---|---------|--------|-----------|
| E1 | `MOV A, 0; DIV A; HLT` | F=1, A=1 | ERR_DIV_ZERO (1) |
| E2 | Push with SP=0: `MOV SP, 0; PUSH A; HLT` | F=1, A=2 | ERR_STACK_OVERFLOW (2) |
| E3 | Pop with SP=231: `MOV SP, 231; POP A; HLT` | F=1, A=3 | ERR_STACK_UNDERFLOW (3) |
| E4 | Invalid reg byte in encoded instruction | F=1, A=4 | ERR_INVALID_REG (4) |
| E5 | `MOV A, [255]; ADD A, [A]; HLT` (indirect OOB: reg value + offset > 255) | F=1, A=5 | ERR_PAGE_BOUNDARY (5) |
| E6 | Execute unassigned opcode byte (e.g., DB 0xFF at IP) | F=1, A=6 | ERR_INVALID_OPCODE (6) |
| E7 | FP instruction with invalid FPM byte encoding | F=1, A=12 | ERR_FP_FORMAT (12) |
| E8 | `VSET VA, 0xFF, 0xFE; VSET VL, 0, 2; VADD.U VC, VA, 1; VWAIT; HLT` | F=1, A=13 | ERR_VU_OOB (13) |
| E9 | `VSET VL, 0, 4; VDOT.U VC, VA, VB; VWAIT; HLT` | F=1, A=14 | ERR_VU_FORMAT (14) |

---

## E.2 Fault State Machine — Invariants

### E.2.1 F Flag and A Register

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E10 | `MOV A, 0; DIV A; HLT` | F=1, A=1 | F set, A=error code |
| E11 | `MOV A, 42; DIV A; HLT` | F=1, A=1 | Original A (42) overwritten by error code |
| E12 | `HLT` (no fault) | F=0, A=0 | No fault → F=0, A unchanged |

### E.2.2 Z and C Preserved Across Fault

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E13 | `ADD A, A` (set Z=1, C=0) | Z=1, C=0 after fault | Z/C survive fault |
|     | `MOV A, 0; DIV A; HLT` | F=1, A=1 | |
| E14 | `MOV A, 0xFF; ADD A, 1` (set Z=0, C=1) | Z=0, C=1 after fault | |
|     | `MOV A, 0; DIV A; HLT` | F=1, A=1 | |
| E15 | `MOV A, 1; CMP A, 2` (set Z=0, C=1) | Z=0, C=1 after fault | CMP flags preserved |
|     | `PUSH A` with SP=0; `HLT` | F=1, A=2 | |

### E.2.3 IP Frozen After Fault

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E16 | `MOV A, 0; DIV A; HLT` | IP = address of `DIV A` | IP stops at faulting instruction |
| E17 | Deferred VU fault: `VADD.U...; VWAIT; HLT` where VU faults | IP = address of `VWAIT` | Deferred fault stops at VWAIT |

### E.2.4 CPU Stops After Fault (No Further Execution)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E18 | `MOV A, 0; DIV A; MOV B, 99; HLT` | B=0 (initial) | Instructions after fault not executed |
| E19 | `MOV A, 0; DIV A; ADD A, 10; HLT` | A=1 (error code, not 11) | A stays as error code |

---

## E.3 Pre-Check Atomicity

Faults must fire **before** any state modification (no partial writes).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E20 | PUSH with SP=0: `MOV B, 99; MOV SP, 0; PUSH B; HLT` | mem[0]=0 (not 99), SP=0 | PUSH faults before write |
| E21 | Page OOB: `MOV A, 250; MOV [A+10], 42; HLT` (offset 260 > 255) | mem unchanged | No write on page fault |
| E22 | DIV: `MOV A, 5; MOV B, 0; DIV B; HLT` | A=1 (ERR_DIV_ZERO, not 5) | DIV faults before quotient written |

---

## E.4 Reserved Codes Not Produced

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E23 | Exhaust all known fault conditions | A ∈ {1,2,3,4,5,6,12,13,14} | Codes 7–11 never appear in v3 |

---

## E.5 FP Exception vs FAULT Distinction

FP arithmetic exceptions set FPSR flags but do NOT set F=1.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E24 | `FDIV.F FA, [zero]` (divide FP by 0.0) | F=0, FPSR.DZ=1 | FP DivZero → flag only, no FAULT |
| E25 | `FADD.F FA, [nan]` (NaN input) | F=0, FPSR.NV=1 | FP NaN → flag only, no FAULT |
| E26 | Invalid FPM byte (bad fmt field) | F=1, A=12 | ERR_FP_FORMAT → FAULT |

---

## E.6 VU Exception vs FAULT Distinction

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| E27 | `VDIV.F VC, VA, VB` where VB[i]=0.0 → +inf | F=0, VFPSR.DZ=1 | VU FP DivZero → VFPSR flag, no FAULT |
| E28 | `VDIV.U VC, VA, VB` where VB[i]=0 → ERR_DIV_ZERO | F=1, A=1 at VWAIT | VU int DivZero → deferred FAULT |
| E29 | `VSQRT.U VC, VA; VWAIT` | F=1, A=14 | ERR_VU_FORMAT at decode, immediate |
