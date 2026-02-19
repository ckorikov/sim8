# 6. Test Specification

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [Assembler](asm.md), [Microarchitecture](uarch.md), [FPU](fp.md), [FP Tests](tests-fp.md)

## 6.1 Test Methodology

Each test follows the pattern: **assemble** source code, **execute** until HLT or fault, **verify** CPU state.

Verification targets:

| Target | Description |
|--------|-------------|
| `A`, `B`, `C`, `D` | Register values (0-255) |
| `SP` | Stack pointer value |
| `IP` | Instruction pointer (address of HLT opcode when HALTED) |
| `Z` | Zero flag (true/false) |
| `C` | Carry flag (true/false) |
| `F` | Fault flag (true/false) |
| `mem[addr]` | Memory byte at address |
| `fault` | CPU entered FAULT state (F=true, A=error code) |
| `error` | Assembler returned error with line number |

Assembler-only tests assemble source and verify either:

- successful output (machine code bytes and resolved labels), or
- an error that includes the source line number.

CPU tests load assembled code into memory, execute instructions until HALT or FAULT, then check state. On FAULT, verify F=true and A contains the expected [error code](errors.md).

---

## 6.2 MOV — Data Movement

Tests opcodes 1-8. MOV must **not** affect flags.

### 6.2.1 Register-to-Register

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 1 | `MOV A, 42` | A=42 | Load immediate to register |
|   | `MOV B, A` | B=42 | Copy between GPR |
|   | `HLT` | | |
| 2 | `MOV A, 0xFF` | A=255 | Max byte value |
|   | `MOV B, A` | B=255 | |
|   | `MOV C, B` | C=255 | Chain copy |
|   | `MOV D, C` | D=255 | |
|   | `HLT` | | |
| 3 | `MOV SP, 200` | SP=200 | Write to SP via MOV |
|   | `MOV A, SP` | A=200 | Read SP via MOV |
|   | `HLT` | | |

### 6.2.2 Memory Operations

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 4 | `MOV A, 77` | | |
|   | `MOV [0x50], A` | mem[0x50]=77 | Store register to direct address |
|   | `MOV B, [0x50]` | B=77 | Load from direct address |
|   | `HLT` | | |
| 5 | `MOV [0x50], 99` | mem[0x50]=99 | Store immediate to address |
|   | `MOV A, [0x50]` | A=99 | |
|   | `HLT` | | |
| 6 | `MOV B, 0x50` | | |
|   | `MOV A, 33` | | |
|   | `MOV [B], A` | mem[0x50]=33 | Store via register indirect |
|   | `MOV C, [B]` | C=33 | Load via register indirect |
|   | `HLT` | | |
| 7 | `MOV B, 0x50` | | |
|   | `MOV [B+2], 88` | mem[0x52]=88 | Store immediate via indirect+offset |
|   | `MOV A, [B+2]` | A=88 | Load via indirect+offset |
|   | `HLT` | | |

### 6.2.3 Flag Preservation

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 8 | `MOV A, 255` | | |
|   | `ADD A, 1` | C=true | Carry set by overflow |
|   | `MOV B, 42` | C=true | MOV must not clear carry |
|   | `HLT` | | |
| 9 | `MOV A, 1` | | |
|   | `SUB A, 1` | Z=true | Zero flag set |
|   | `MOV B, 99` | Z=true | MOV must not clear zero |
|   | `HLT` | | |

---

## 6.3 ADD / SUB — Arithmetic

Tests opcodes 10-13 (ADD), 14-17 (SUB). All set flags according to the flag rules in the ISA.

### 6.3.1 Basic Arithmetic

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 10 | `MOV A, 3` | | |
|    | `MOV B, 5` | | |
|    | `ADD A, B` | A=8, Z=false, C=false | Reg + reg |
|    | `HLT` | | |
| 11 | `MOV A, 10` | | |
|    | `ADD A, 20` | A=30 | Reg + const |
|    | `HLT` | | |
| 12 | `MOV A, 10` | | |
|    | `MOV B, 3` | | |
|    | `SUB A, B` | A=7, C=false | Reg - reg, positive |
|    | `HLT` | | |
| 13 | `MOV A, 10` | | |
|    | `SUB A, 20` | A=246, C=true | Unsigned underflow wraps |
|    | `HLT` | | |

### 6.3.2 Overflow / Underflow

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 14 | `MOV A, 200` | | |
|    | `ADD A, 100` | A=44, C=true | 300 % 256 = 44, carry set |
|    | `HLT` | | |
| 15 | `MOV A, 0` | | |
|    | `SUB A, 1` | A=255, C=true | 0 - 1 wraps to 255 |
|    | `HLT` | | |
| 16 | `MOV A, 128` | | |
|    | `ADD A, 128` | A=0, C=true, Z=true | 256 wraps to 0; both flags set |
|    | `HLT` | | |

### 6.3.3 SP Arithmetic

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 17 | `MOV SP, 100` | | |
|    | `ADD SP, 10` | SP=110 | ADD with SP as destination |
|    | `HLT` | | |
| 18 | `MOV SP, 100` | | |
|    | `MOV A, 30` | | |
|    | `SUB SP, A` | SP=70 | SUB with SP as destination |
|    | `HLT` | | |

### 6.3.4 Addressing Modes

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 19 | `MOV [0x50], 25` | | |
|    | `MOV A, 10` | | |
|    | `ADD A, [0x50]` | A=35 | Add from direct address |
|    | `HLT` | | |
| 20 | `MOV B, 0x50` | | |
|    | `MOV [0x50], 7` | | |
|    | `MOV A, 3` | | |
|    | `ADD A, [B]` | A=10 | Add from register indirect |
|    | `HLT` | | |

---

## 6.4 INC / DEC

Tests opcodes 18-19. Set flags.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 21 | `MOV A, 0` | | |
|    | `INC A` | A=1, Z=false, C=false | Basic increment |
|    | `HLT` | | |
| 22 | `MOV A, 255` | | |
|    | `INC A` | A=0, Z=true, C=true | Overflow 255→0 |
|    | `HLT` | | |
| 23 | `MOV A, 1` | | |
|    | `DEC A` | A=0, Z=true | Decrement to zero |
|    | `HLT` | | |
| 24 | `MOV A, 0` | | |
|    | `DEC A` | A=255, Z=false, C=true | Underflow 0→255 |
|    | `HLT` | | |
| 25 | `INC SP` | SP=232 | INC with SP (initial 231 + 1) |
|    | `HLT` | | |

---

## 6.5 CMP — Compare

Tests opcodes 20-23. Sets flags without modifying destination.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 26 | `MOV A, 5` | | |
|    | `CMP A, 5` | Z=true, C=false, A=5 | Equal: Z=1, A unchanged |
|    | `HLT` | | |
| 27 | `MOV A, 3` | | |
|    | `CMP A, 10` | Z=false, C=true, A=3 | Less than: C=1 |
|    | `HLT` | | |
| 28 | `MOV A, 10` | | |
|    | `CMP A, 3` | Z=false, C=false, A=10 | Greater than: both clear |
|    | `HLT` | | |
| 29 | `MOV A, 0` | | |
|    | `CMP A, 0` | Z=true, C=false | Zero equals zero |
|    | `HLT` | | |

---

## 6.6 JMP / Conditional Jumps

Tests opcodes 30-43. Jumps do not affect flags.

### 6.6.1 Unconditional Jump

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 30 | `JMP end` | A=0 | Jump skips MOV |
|    | `MOV A, 99` | | (should not execute) |
|    | `end: HLT` | | |
| 31 | `MOV B, end` | A=0 | Jump via register |
|    | `JMP B` | | |
|    | `MOV A, 99` | | |
|    | `end: HLT` | | |

**Note on test 31:** `MOV B, end` loads the address of label `end` into B. The label's value is resolved by the assembler.

### 6.6.2 Conditional Jumps

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 32 | `MOV A, 5` | | |
|    | `CMP A, 5` | | Z=1 |
|    | `JZ equal` | | Should jump |
|    | `MOV B, 1` | | |
|    | `equal: HLT` | B=0 | B untouched → jump taken |
| 33 | `MOV A, 5` | | |
|    | `CMP A, 3` | | Z=0 |
|    | `JZ skip` | | Should not jump |
|    | `MOV B, 1` | | |
|    | `skip: HLT` | B=1 | B set → jump not taken |
| 34 | `MOV A, 5` | | |
|    | `CMP A, 3` | | Z=0 |
|    | `JNZ notzero` | | Should jump |
|    | `MOV B, 1` | | |
|    | `notzero: HLT` | B=0 | |
| 35 | `MOV A, 200` | | |
|    | `ADD A, 100` | | C=1 (overflow) |
|    | `JC overflow` | | Should jump |
|    | `MOV B, 1` | | |
|    | `overflow: HLT` | B=0 | |
| 36 | `MOV A, 5` | | |
|    | `ADD A, 3` | | C=0 |
|    | `JNC nocarry` | | Should jump |
|    | `MOV B, 1` | | |
|    | `nocarry: HLT` | B=0 | |
| 37 | `MOV A, 10` | | |
|    | `CMP A, 3` | | C=0, Z=0 → above |
|    | `JA above` | | Should jump |
|    | `MOV B, 1` | | |
|    | `above: HLT` | B=0 | |
| 38 | `MOV A, 3` | | |
|    | `CMP A, 10` | | C=1 → not above |
|    | `JNA notabove` | | Should jump |
|    | `MOV B, 1` | | |
|    | `notabove: HLT` | B=0 | |

### 6.6.3 Jump Aliases

Each alias must produce the same opcode as its canonical form.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 39 | `JB label` / `JNAE label` / `JC label` | Same bytecode | All map to opcodes 32/33 |
| 40 | `JNB label` / `JAE label` / `JNC label` | Same bytecode | All map to opcodes 34/35 |
| 41 | `JE label` / `JZ label` | Same bytecode | Both map to opcodes 36/37 |
| 42 | `JNE label` / `JNZ label` | Same bytecode | Both map to opcodes 38/39 |
| 43 | `JNBE label` / `JA label` | Same bytecode | Both map to opcodes 40/41 |
| 44 | `JBE label` / `JNA label` | Same bytecode | Both map to opcodes 42/43 |

Test logic: assemble each alias variant, compare the resulting machine-code byte sequences — they must be identical.

---

## 6.7 Stack Operations — PUSH / POP

Tests opcodes 50-54. SP starts at 231 (0xE7).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 45 | `PUSH 42` | mem[231]=42, SP=230 | Push constant |
|    | `HLT` | | |
| 46 | `MOV A, 77` | | |
|    | `PUSH A` | mem[231]=77, SP=230 | Push register |
|    | `HLT` | | |
| 47 | `PUSH 10` | | |
|    | `PUSH 20` | | |
|    | `POP A` | A=20 | LIFO order |
|    | `POP B` | B=10, SP=231 | SP restored |
|    | `HLT` | | |
| 48 | `MOV B, 0x50` | | |
|    | `MOV [0x50], 88` | | |
|    | `PUSH [B]` | mem[231]=88 | Push from register indirect |
|    | `HLT` | | |
| 49 | `PUSH [0x50]` | | Push from direct address |
|    | `HLT` | | (verify mem[231] = mem[0x50]) |

### 6.7.1 Stack Boundaries

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 50 | `MOV SP, 0` / `PUSH 1` | F=true, A=2 | Stack overflow (ERR_STACK_OVERFLOW) |
| 51 | `POP A` | F=true, A=3 | Stack underflow (ERR_STACK_UNDERFLOW) |

Test 50 logic: set SP=0 via `MOV SP, 0`, then execute `PUSH 1`. The PUSH finds SP=0 and triggers **FAULT (A=2)** before any memory write or SP change (see [Error Codes](errors.md)).

Test 51 logic: POP on initial state triggers **FAULT (A=3)** (validation happens before SP increment or memory read; see [Error Codes](errors.md)).

---

## 6.8 CALL / RET — Subroutines

Tests opcodes 55-57.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 52 | `CALL func` | A=42 | Basic call and return |
|    | `HLT` | | |
|    | `func: MOV A, 42` | | |
|    | `RET` | | Returns to HLT |
| 53 | `PUSH 10` | | |
|    | `CALL func` | A=10, SP=231 | Stack consistent after call/ret |
|    | `POP A` | | A gets the 10 from before CALL |
|    | `HLT` | | |
|    | `func: RET` | | |
| 54 | `CALL f1` | A=2 | Nested calls |
|    | `HLT` | | |
|    | `f1: CALL f2` | | |
|    | `INC A` | | A=1→2 after f2 returns |
|    | `RET` | | |
|    | `f2: MOV A, 1` | | |
|    | `RET` | | |
| 55 | `MOV B, func` | A=77 | CALL via register |
|    | `CALL B` | | |
|    | `HLT` | | |
|    | `func: MOV A, 77` | | |
|    | `RET` | | |

### 6.8.1 Return Address Verification

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 56 | `CALL func` | | CALL pushes address of next instruction |
|    | `MOV A, 99` | A=99 | This is where RET must return |
|    | `HLT` | | |
|    | `func: RET` | | |

---

## 6.9 MUL / DIV

Tests opcodes 60-67. Implicit accumulator: `A = A op operand`.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 57 | `MOV A, 6` | | |
|    | `MOV B, 7` | | |
|    | `MUL B` | A=42 | 6 * 7 |
|    | `HLT` | | |
| 58 | `MOV A, 200` | | |
|    | `MUL 2` | A=144, C=true | 400 % 256 = 144, carry |
|    | `HLT` | | |
| 59 | `MOV A, 20` | | |
|    | `MOV B, 4` | | |
|    | `DIV B` | A=5 | 20 / 4 |
|    | `HLT` | | |
| 60 | `MOV A, 7` | | |
|    | `DIV 2` | A=3 | Integer division truncates |
|    | `HLT` | | |
| 61 | `MOV A, 10` | | |
|    | `DIV 0` | F=true, A=1 | Division by zero (ERR_DIV_ZERO) |
|    | `HLT` | | |
| 62 | `MOV A, 0` | | |
|    | `MUL 100` | A=0, Z=true | Zero result sets Z flag |
|    | `HLT` | | |
| 63 | `MOV B, 0x50` | | |
|    | `MOV [0x50], 7` | | |
|    | `MOV A, 6` | | |
|    | `MUL [B]` | A=42 | MUL via register indirect (opcode 61) |
|    | `HLT` | | |
| 64 | `MOV [0x50], 5` | | |
|    | `MOV A, 8` | | |
|    | `MUL [0x50]` | A=40 | MUL via direct address (opcode 62) |
|    | `HLT` | | |
| 65 | `MOV B, 0x50` | | |
|    | `MOV [0x50], 4` | | |
|    | `MOV A, 20` | | |
|    | `DIV [B]` | A=5 | DIV via register indirect (opcode 65) |
|    | `HLT` | | |
| 66 | `MOV [0x50], 3` | | |
|    | `MOV A, 15` | | |
|    | `DIV [0x50]` | A=5 | DIV via direct address (opcode 66) |
|    | `HLT` | | |

---

## 6.10 Bitwise — AND / OR / XOR / NOT

Tests opcodes 70-82. GPR only (SP not allowed).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 67 | `MOV A, 0xFF` | | |
|    | `AND A, 0x0F` | A=0x0F, C=false | Mask lower nibble |
|    | `HLT` | | |
| 68 | `MOV A, 0xF0` | | |
|    | `OR A, 0x0F` | A=0xFF, C=false | Combine bits |
|    | `HLT` | | |
| 69 | `MOV A, 0xFF` | | |
|    | `XOR A, 0xFF` | A=0, Z=true, C=false | XOR self = zero |
|    | `HLT` | | |
| 70 | `MOV A, 0` | | |
|    | `NOT A` | A=255, C=false | ~0 = 255 (C cleared) |
|    | `HLT` | | |
| 71 | `MOV A, 0x0F` | | |
|    | `NOT A` | A=0xF0, C=false | ~15 = 240 (C cleared) |
|    | `HLT` | | |
| 72 | `MOV A, 0xFF` | | |
|    | `NOT A` | A=0, Z=true, C=false | ~255 = 0 (C cleared) |
|    | `HLT` | | |

---

## 6.11 Shift — SHL / SHR

Tests opcodes 90-97. GPR only.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 73 | `MOV A, 1` | | |
|    | `SHL A, 1` | A=2 | Shift left by 1 |
|    | `HLT` | | |
| 74 | `MOV A, 1` | | |
|    | `SHL A, 7` | A=128 | 1 << 7 |
|    | `HLT` | | |
| 75 | `MOV A, 128` | | |
|    | `SHL A, 1` | A=0, C=true | Overflow: 256 → 0 |
|    | `HLT` | | |
| 76 | `MOV A, 128` | | |
|    | `SHR A, 1` | A=64 | Unsigned right shift |
|    | `HLT` | | |
| 77 | `MOV A, 1` | | |
|    | `SHR A, 1` | A=0, Z=true, C=true | Bit shifted out (1 % 2 ≠ 0) |
|    | `HLT` | | |
| 78 | `MOV A, 3` | | |
|    | `SAL A, 2` | A=12 | SAL alias = SHL |
|    | `HLT` | | |
| 79 | `MOV A, 12` | | |
|    | `SAR A, 2` | A=3 | SAR alias = SHR |
|    | `HLT` | | |
| 80 | `MOV A, 200` | | |
|    | `ADD A, 100` | | C=true from overflow |
|    | `SHL A, 0` | A=44, C=true | Shift by 0: C preserved, value unchanged |
|    | `HLT` | | |

---

## 6.12 Addressing Modes

Cross-instruction tests to verify all addressing modes work consistently.

### 6.12.1 Register Indirect with Offset

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 81 | `MOV B, 0x50` | | |
|    | `MOV [B+0], 10` | mem[0x50]=10 | Offset 0 (simple indirect) |
|    | `MOV [B+5], 20` | mem[0x55]=20 | Positive offset |
|    | `MOV [B-3], 30` | mem[0x4D]=30 | Negative offset |
|    | `HLT` | | |
| 82 | `MOV [SP-1], 42` | mem[230]=42 | SP-relative addressing |
|    | `MOV A, [SP-1]` | A=42 | |
|    | `HLT` | | |

### 6.12.2 Offset Encoding Boundary

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 83 | `MOV B, 0x50` | | |
|    | `MOV [B+15], 1` | mem[0x5F]=1 | Max positive offset |
|    | `MOV A, [B+15]` | A=1 | |
|    | `HLT` | | |
| 84 | `MOV B, 0x50` | | |
|    | `MOV [B-16], 2` | mem[0x40]=2 | Max negative offset |
|    | `MOV A, [B-16]` | A=2 | |
|    | `HLT` | | |

---

## 6.13 Flag Behavior

Comprehensive flag tests for arithmetic flag behavior.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 85 | `MOV A, 5` | | |
|    | `ADD A, 0` | Z=false, C=false | Positive result: both clear |
|    | `HLT` | | |
| 86 | `MOV A, 0` | | |
|    | `ADD A, 0` | Z=true, C=false | Zero result: Z=1 |
|    | `HLT` | | |
| 87 | `MOV A, 255` | | |
|    | `ADD A, 1` | A=0, Z=true, C=true | Overflow: 256 wraps to 0, both flags set |
|    | `HLT` | | |
| 88 | `MOV A, 0` | | |
|    | `SUB A, 1` | Z=false, C=true | Underflow: C=1, value=255 |
|    | `HLT` | | |
| 89 | `MOV A, 128` | | |
|    | `ADD A, 128` | A=0, C=true, Z=true | 256 wraps to 0; both flags set |
|    | `HLT` | | |

**Test 89 detail:** When an arithmetic operation overflows/underflows and wraps to a result of 0, both C and Z may be set simultaneously.

---

## 6.14 SP Operand Restrictions

Verify that SP (code 4) is accepted where allowed and rejected where not.

### 6.14.1 Allowed (Assembler accepts, CPU executes)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 90 | `MOV SP, 100` | SP=100 | MOV to SP |
|    | `HLT` | | |
| 91 | `MOV SP, 100` | | |
|    | `ADD SP, 10` | SP=110 | ADD with SP |
|    | `HLT` | | |
| 92 | `MOV SP, 100` | | |
|    | `SUB SP, 5` | SP=95 | SUB with SP |
|    | `HLT` | | |
| 93 | `INC SP` | SP=232 | INC SP (initial 231 + 1) |
|    | `HLT` | | |
| 94 | `DEC SP` | SP=230 | DEC SP (initial 231 − 1) |
|    | `HLT` | | |
| 95 | `CMP SP, 231` | Z=true | CMP with SP |
|    | `HLT` | | |

### 6.14.2 Rejected at Runtime

These forms must not execute successfully. They may be rejected at assembly time, or enter **FAULT (A=4)** at runtime with an "Invalid register" error (see [Error Codes](errors.md)).

**Fault invariant:** Any runtime FAULT must provide an error code in register `A` (see [Error Codes](errors.md)). For the cases below, a runtime fault must be `ERR_INVALID_REG` (A=4).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 96 | `PUSH SP` | fault **or** error | SP not supported for PUSH |
| 97 | `POP SP` | fault **or** error | SP not supported for POP |
| 98 | `AND SP, 0xFF` | fault **or** error | Bitwise: GPR only |
| 99 | `OR SP, 0` | fault **or** error | |
| 100 | `XOR SP, SP` | fault **or** error | |
| 101 | `NOT SP` | fault **or** error | |
| 102 | `SHL SP, 1` | fault **or** error | Shift: GPR only |
| 103 | `SHR SP, 1` | fault **or** error | |
| 104 | `MUL SP` | fault **or** error | MUL: GPR only |
| 105 | `DIV SP` | fault **or** error | DIV: GPR only |

---

## 6.15 Memory-Mapped I/O

Console display region: addresses 232-255 (0xE8-0xFF).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 106 | `MOV [232], 72` | mem[232]=72 | Write 'H' to first display cell |
|     | `MOV [233], 105` | mem[233]=105 | Write 'i' to second cell |
|     | `HLT` | display = "Hi" | |
| 107 | `MOV A, 65` | | |
|     | `MOV [0xFF], A` | mem[255]=65 | Write to last display cell |
|     | `HLT` | | |
| 108 | `MOV A, [232]` | A = mem[232] | Read from display region |
|     | `HLT` | | (region is readable) |
| 109 | `MOV DP, 5` | | DP=5 (not page 0) |
|     | `MOV [232], 72` | mem[1512]=72 | Writes to page 5 (5×256+232), NOT I/O |
|     | `HLT` | display unchanged | I/O only accessible when DP=0 |

---

## 6.16 Assembler — Encoding

Verify assembler produces correct bytecode for each instruction format.

### 6.16.1 Bytecode Verification

| # | Source | Expected bytes | Description |
|---|--------|--------------------|-------------|
| 110 | `HLT` | `[0]` | 1-byte instruction |
| 111 | `RET` | `[57]` | 1-byte instruction |
| 112 | `MOV A, B` | `[1, 0, 1]` | 3-byte: opcode, dest, src |
| 113 | `MOV A, 42` | `[6, 0, 42]` | 3-byte: opcode, reg, const |
| 114 | `INC C` | `[18, 2]` | 2-byte: opcode, reg |
| 115 | `JMP 100` | `[31, 100]` | 2-byte: opcode, addr |
| 116 | `PUSH 255` | `[53, 255]` | 2-byte: opcode, const |
| 117 | `ADD A, [B+2]` | `[11, 0, 17]` | regaddr: (2<<3)\|1 = 17 |
| 118 | `MOV A, [SP-1]` | `[3, 0, 252]` | regaddr: (31<<3)\|4 = 252 |
| 119 | `DB 0` | `[0]` | Raw byte |
| 120 | `DB "Hi"` | `[72, 105]` | String to ASCII bytes |

### 6.16.2 Number Formats

| # | Source | Expected bytes | Description |
|---|--------|--------------------|-------------|
| 121 | `MOV A, 200` | `[6, 0, 200]` | Decimal |
| 122 | `MOV A, 200d` | `[6, 0, 200]` | Decimal explicit |
| 123 | `MOV A, 0xC8` | `[6, 0, 200]` | Hexadecimal |
| 124 | `MOV A, 0o310` | `[6, 0, 200]` | Octal |
| 125 | `MOV A, 11001000b` | `[6, 0, 200]` | Binary |
| 126 | `MOV A, 'A'` | `[6, 0, 65]` | Character literal |

### 6.16.3 Labels

| # | Source | Expected | Description |
|---|--------|----------|-------------|
| 127 | `start: JMP start` | Bytes: `[31, 0]`; label `start` = 0 | Label at position 0 |
| 128 | `JMP end` | Bytes: `[31, 2, 0]`; label `end` = 2 | Forward reference |
|     | `end: HLT` | (covered above) | |
| 129 | `.loop: JMP .loop` | Bytes: `[31, 0]`; label `.loop` = 0 | Dot-prefix label |

### 6.16.4 Case Insensitivity

| # | Source | Expected | Description |
|---|--------|----------|-------------|
| 130 | `mov a, 5` | Same as `MOV A, 5` | Mnemonics case-insensitive |
| 131 | `Mov A, 5` | Same bytecode | Mixed case |

---

## 6.17 Assembler — Error Handling

Each error must include the correct source line number (1-based: first line is 1).

| # | Source | Expected Error | Description |
|---|--------|---------------|-------------|
| 132 | `x: DB 0` | `Duplicate label: x` | Two labels with same name |
|     | `x: DB 1` | line: 2 | |
| 133 | `X: DB 0` | `Duplicate label: x` | Case-insensitive duplicate |
|     | `x: DB 1` | line: 2 | |
| 134 | `A: DB 0` | `Label contains keyword: A` | Reserved register name |
|     | | line: 1 | |
| 135 | `B: DB 0` | `Label contains keyword: B` | |
| 136 | `JMP nowhere` | `Undefined label: nowhere` | Label never defined |
| 137 | `MOV A, 0xZZ` | `Invalid number format` | Bad hex |
|     | | line: 1 | |
| 138 | `MOV A, 256` | `must have a value between 0-255` | Out of byte range |
| 139 | `MOV A, [B+16]` | `offset must be a value between -16...+15` | Offset too large |
| 140 | `MOV A, [B-17]` | `offset must be a value between -16...+15` | Offset too small |
| 141 | `MOV A, 'AB'` | `Only one character is allowed` | Multi-char literal |
| 142 | `ADD 5, A` | `ADD does not support this operand` | Invalid operand type |
| 143 | `INC A, B` | `INC: too many arguments` | Extra operand |
| 144 | `DB [0x50]` | `DB does not support this operand` | Invalid DB operand |
| 145 | `FOO A` | `Invalid instruction: FOO` | Unknown mnemonic |
| 146 | `???` | `Syntax error` | Unparseable line |

### 6.17.1 Line Number Accuracy

| # | Source | Expected line | Description |
|---|--------|-------------|-------------|
| 147 | `MOV A, 1` | line: 3 | Error on third line (1-based) |
|     | `MOV B, 2` | | |
|     | `FOO` | | |
| 148 | `; comment` | line: 2 | Blank/comment lines counted |
|     | `FOO` | | |

---

## 6.18 Assembler — Source Mapping

The `mapping` output maps code positions to source line numbers (1-based). DB is excluded.

| # | Source | Expected `mapping` | Description |
|---|--------|--------------------|-------------|
| 149 | `MOV A, 1` | {0: 1, 3: 2} | Two 3-byte instructions |
|     | `MOV B, 2` | | positions 0 and 3 |
| 150 | `DB 42` | {1: 2} | DB at pos 0 excluded |
|     | `INC A` | | INC at pos 1 mapped |
| 151 | `label: HLT` | {0: 1} | Label doesn't consume code bytes |

---

## 6.19 Integration — End-to-End Programs

Full programs testing multiple subsystems together.

| # | Program | Verify | Description |
|---|---------|--------|-------------|
| 152 | **Counter** | A=5 | Loop with INC and CMP |
|     | `MOV A, 0` | |
|     | `loop: INC A` | |
|     | `CMP A, 5` | |
|     | `JNZ loop` | |
|     | `HLT` | |
| 153 | **Sum 1..10** | A=55 | Accumulator loop |
|     | `MOV A, 0` | |
|     | `MOV B, 1` | |
|     | `loop: ADD A, B` | |
|     | `INC B` | |
|     | `CMP B, 11` | |
|     | `JNZ loop` | |
|     | `HLT` | |
| 154 | **Factorial 5** | A=120 | Subroutine + multiplication |
|     | `MOV A, 1` | |
|     | `MOV B, 5` | |
|     | `loop: MUL B` | |
|     | `DEC B` | |
|     | `CMP B, 1` | |
|     | `JA loop` | |
|     | `HLT` | |
| 155 | **Hello** | display="Hello" | Memory-mapped I/O |
|     | `MOV A, 0` | |
|     | `MOV B, 232` | |
|     | `MOV C, hello` | |
|     | `.loop: MOV A, [C]` | |
|     | `CMP A, 0` | |
|     | `JZ .end` | |
|     | `MOV [B], A` | |
|     | `INC B` | |
|     | `INC C` | |
|     | `JMP .loop` | |
|     | `.end: HLT` | |
|     | `hello: DB "Hello"` | |
|     | `DB 0` | |
| 156 | **Stack frame** | A=30 | CALL/RET with stack params |
|     | `PUSH 10` | |
|     | `PUSH 20` | |
|     | `CALL add_two` | |
|     | `HLT` | |
|     | `add_two:` | |
|     | `MOV A, [SP+2]` | | return addr at SP+1, first arg at SP+2 |
|     | `ADD A, [SP+3]` | | second arg at SP+3 |
|     | `RET` | |

---

## 6.20 Fault Conditions and Edge Cases

### 6.20.1 Invalid Opcode

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 157 | `JMP test` | F=true, A=6 | Invalid opcode (ERR_INVALID_OPCODE) |
|     | `test: DB 9` | | Opcode 9 is not assigned |

### 6.20.2 Page Boundary Violation

Offset calculation outside 0–255 triggers **FAULT (A=5)**. See [addressing modes](isa.md#14-addressing-modes) and [Error Codes](errors.md).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 158 | `MOV B, 250` | F=true, A=5 | Page boundary (ERR_PAGE_BOUNDARY) |
|     | `MOV A, [B+15]` | | 250 + 15 = 265 > 255 |
| 159 | `MOV B, 5` | F=true, A=5 | Page boundary (ERR_PAGE_BOUNDARY) |
|     | `MOV A, [B-10]` | | 5 − 10 = −5 < 0 |

### 6.20.3 SP as Source Operand

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 160 | `MOV SP, 100` | | |
|     | `MOV A, 5` | | |
|     | `ADD A, SP` | A=105 | SP as source in ADD |
|     | `HLT` | | |

---

## 6.21 DP Register — Paged Memory Access

Tests for Data Page register. See [memory model](isa.md#13-memory-model).

### 6.21.1 Basic DP Operations

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 161 | `MOV DP, 0` | DP=0 | Write to DP |
|     | `MOV A, DP` | A=0 | Read from DP |
|     | `HLT` | | |
| 162 | `MOV DP, 255` | DP=255 | Max DP value (page 255) |
|     | `HLT` | | |
| 163 | `MOV DP, 128` | | Mid-range page |
|     | `MOV B, 0` | | |
|     | `MOV [B], 42` | mem[0x8000]=42 | Page 128, offset 0 |
|     | `HLT` | | |

### 6.21.2 Paged Memory Access via Register Indirect

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 164 | `MOV DP, 0` | | Page 0 |
|     | `MOV B, 0x50` | | |
|     | `MOV [B], 42` | mem[0x050]=42 | Write to page 0 |
|     | `HLT` | | |
| 165 | `MOV DP, 1` | | Page 1 |
|     | `MOV B, 0x50` | | |
|     | `MOV [B], 99` | mem[0x150]=99 | Write to page 1 |
|     | `MOV A, [B]` | A=99 | Read from page 1 |
|     | `HLT` | | |
| 166 | `MOV DP, 2` | | Page 2 |
|     | `MOV B, 0` | | |
|     | `MOV [B+10], 77` | mem[0x20A]=77 | Page 2, offset 10 |
|     | `HLT` | | |

### 6.21.3 Direct Addressing Uses DP

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 167 | `MOV [0x50], 11` | mem[0x50]=11 | DP=0, store to page 0 |
|     | `MOV DP, 1` | | Switch to page 1 |
|     | `MOV [0x50], 22` | mem[0x150]=22 | Store to page 1 |
|     | `MOV A, [0x50]` | A=22 | Read from page 1 |
|     | `MOV DP, 0` | | Back to page 0 |
|     | `MOV B, [0x50]` | B=11 | Read from page 0 |
|     | `HLT` | | |

### 6.21.4 SP-Relative Always Page 0

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 168 | `MOV DP, 1` | | Switch to page 1 |
|     | `MOV [SP-1], 55` | mem[230]=55 | SP-relative ignores DP |
|     | `MOV A, [SP-1]` | A=55 | Read from page 0 |
|     | `HLT` | | |

### 6.21.5 Page Boundary Violation with DP

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 169 | `MOV DP, 1` | F=true, A=5 | Page boundary (ERR_PAGE_BOUNDARY) |
|     | `MOV B, 250` | | 250 + 10 = 260 > 255 |
|     | `MOV [B+10], 33` | | |

### 6.21.6 Integration: Cross-Page Data Copy

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 170 | `MOV DP, 1` | | Source page |
|     | `MOV B, 0` | | |
|     | `MOV [B], 0xAA` | | Store 0xAA at page 1, offset 0 |
|     | `MOV A, [B]` | | Load from page 1 |
|     | `MOV DP, 2` | | Dest page |
|     | `MOV [B], A` | mem[0x200]=0xAA | Copy to page 2, offset 0 |
|     | `HLT` | | |

---

## 6.22 Robustness Tests (Adversarial Scenarios)

These tests verify CPU robustness against unusual but valid programming patterns. All scenarios must either execute correctly or terminate with appropriate FAULT.

### 6.22.1 Self-Modifying Code

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 171 | `MOV [20], 0` | IP=20 at halt | Self-mod: write HLT to addr 20 |
|     | `JMP 20` | state=HALTED | then jump there |
|     | `MOV A, 255` | A=0 | unreachable code not executed |
|     | `HLT` | | |

### 6.22.2 Stack Boundary Attacks

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 172 | `POP A` | F=true, A=3 | Empty stack underflow |
|     | | state=FAULT | ERR_STACK_UNDERFLOW |
| 173 | `MOV SP, 0` | F=true, A=2 | Stack overflow |
|     | `PUSH 1` | state=FAULT | ERR_STACK_OVERFLOW |

### 6.22.3 Invalid Opcode Execution

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 174 | `DB 9` | F=true, A=6 | Opcode 9 not assigned |
|     | | state=FAULT | ERR_INVALID_OPCODE |
| 175 | `DB 99` | F=true, A=6 | Opcode 99 not assigned |
|     | | state=FAULT | ERR_INVALID_OPCODE |

### 6.22.4 Division by Zero (Self-Division)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 176 | `DIV A` | F=true, A=1 | A=0 initially, 0/0 = FAULT |
|     | | state=FAULT | ERR_DIV_ZERO |
| 177 | `MOV B, 0` | F=true, A=1 | Divide by zero register |
|     | `DIV B` | state=FAULT | ERR_DIV_ZERO |

### 6.22.5 Invalid Register Codes

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 178 | `DB 70, 6, 0` | F=true, A=4 | AND with reg code 6 (invalid) |
|     | | state=FAULT | ERR_INVALID_REG |
| 179 | `DB 82, 5` | F=true, A=4 | NOT with reg code 5 (DP invalid for NOT) |
|     | | state=FAULT | ERR_INVALID_REG |

### 6.22.6 Code Overwrite via Stack

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 180 | `MOV SP, 5` | A=42 | Stack overwrites code area |
|     | `PUSH 0` | | writes HLT (0) to addr 5 |
|     | `MOV A, 42` | | this executes |
|     | `JMP 5` | | jump to overwritten HLT |
|     | `MOV A, 99` | | unreachable |

### 6.22.7 Execution from High Memory

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 181 | `MOV [200], 6` | A=77 | Write MOV A, 77 to addr 200 |
|     | `MOV [201], 0` | | reg A |
|     | `MOV [202], 77` | | value 77 |
|     | `MOV [203], 0` | | HLT at 203 |
|     | `JMP 200` | IP=203 | execute from high address |

### 6.22.8 DB Comma-Separated List

| # | Source | Expected bytes | Description |
|---|--------|----------------|-------------|
| 182 | `DB 10, 20, 30` | `[10, 20, 30]` | Comma-separated list |
| 183 | `DB 0xFF, 0, 42` | `[255, 0, 42]` | Mixed number formats in list |
| 184 | `DB 1` | `[1]` | Single value (unchanged behavior) |

---

## 6.23 Coverage Completeness

Additional tests for edge cases and opcode variants identified by specification audit.

### 6.23.1 Instruction Fetch Boundary

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 185 | `MOV [254], 13` | F=true, A=5 | 3-byte opcode at IP=254 crosses page boundary |
|     | `MOV [255], 0` | state=FAULT | IP+len = 254+3 = 257 >= 256 → FAULT(5) |
|     | `JMP 254` | | ERR_PAGE_BOUNDARY from fetch |

### 6.23.2 DP Rejection in Non-MOV

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 186 | `DB 13, 5, 1` | F=true, A=4 | ADD with reg_code=5 (DP) → FAULT(4) |
|     | | state=FAULT | ERR_INVALID_REG: DP invalid for ADD |

### 6.23.3 DIV Always Clears Carry

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 187 | `MOV A, 200` | | |
|     | `ADD A, 100` | | A=44, C=true (overflow) |
|     | `MOV A, 10` | | |
|     | `DIV 2` | A=5, C=false | DIV clears C regardless of prior state |
|     | `HLT` | | |

### 6.23.4 Shift by Count >= 8

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 188 | `MOV A, 255` | | |
|     | `SHL A, 8` | A=0, Z=true, C=true | Shift by 8: result=0, C=1 (nonzero value) |
|     | `HLT` | | |

### 6.23.5 CMP Addressing Modes

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 189 | `MOV A, 10` | | |
|     | `MOV B, 10` | | |
|     | `CMP A, B` | Z=true, C=false | CMP reg, reg (opcode 20) |
|     | `HLT` | | |
| 190 | `MOV [0x50], 5` | | |
|     | `MOV A, 3` | | |
|     | `CMP A, [0x50]` | Z=false, C=true | CMP reg, [addr] (opcode 22): 3-5 < 0 |
|     | `HLT` | | |

### 6.23.6 SUB Addressing Mode

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 191 | `MOV [0x50], 3` | | |
|     | `MOV A, 10` | | |
|     | `SUB A, [0x50]` | A=7, C=false | SUB reg, [addr] (opcode 16) |
|     | `HLT` | | |

### 6.23.7 CALL/RET Stack Faults

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 192 | `MOV SP, 0` | F=true, A=2 | CALL with SP=0 → stack overflow |
|     | `MOV A, 100` | state=FAULT | ERR_STACK_OVERFLOW (same check as PUSH) |
|     | `CALL A` | | |
| 193 | `RET` | F=true, A=3 | RET on initial state (SP=231) → underflow |
|     | | state=FAULT | ERR_STACK_UNDERFLOW |

### 6.23.8 CALL Return Address Wrapping

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 194 | `MOV [254], 56` | B=0 | CALL at IP=254: return_addr = 256 mod 256 = 0 |
|     | `MOV [255], 20` | | target = addr 20 |
|     | `MOV [20], 54` | | POP B at addr 20 |
|     | `MOV [21], 1` | | reg = B |
|     | `MOV [22], 0` | | HLT at addr 22 |
|     | `JMP 254` | | B gets the wrapped return address (0) |

### 6.23.9 MUL Carry + Zero Simultaneously

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 195 | `MOV A, 128` | | |
|     | `MUL 2` | A=0, C=true, Z=true | 128×2=256 → wraps to 0, carry set |
|     | `HLT` | | |

### 6.23.10 PUSH Source Uses DP

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 196 | `MOV DP, 1` | A=42 | PUSH [reg] reads from DP page |
|     | `MOV B, 0x50` | | |
|     | `MOV [B], 42` | | writes 42 to page 1, offset 0x50 |
|     | `PUSH [B]` | | reads from page 1 via DP |
|     | `MOV DP, 0` | | back to page 0 |
|     | `POP A` | | A=42 (value from page 1) |
|     | `HLT` | | |

### 6.23.11 Execution from I/O Region

Code placed in the I/O region (addresses 232-255) is executable — the CPU enforces the page boundary at 256, not 232.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 197 | `MOV [232], 6` | A=99 | Write MOV A, 99 to I/O region |
|     | `MOV [233], 0` | | reg A |
|     | `MOV [234], 99` | | value 99 |
|     | `MOV [235], 0` | | HLT at 235 |
|     | `JMP 232` | IP=235 | Execute from I/O address space |

---

## 6.24 Opcode Coverage Completeness

Tests for opcode variants not covered by earlier sections.

### 6.24.1 SUB / CMP Register Indirect

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 198 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 3` | | |
|     | `MOV A, 10` | | |
|     | `SUB A, [B]` | A=7, C=false | SUB reg, [reg] (opcode 15) |
|     | `HLT` | | |
| 199 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 5` | | |
|     | `MOV A, 5` | | |
|     | `CMP A, [B]` | Z=true, C=false, A=5 | CMP reg, [reg] (opcode 21) |
|     | `HLT` | | |

### 6.24.2 Conditional Jumps via Register

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 200 | `MOV A, 5` | | |
|     | `CMP A, 5` | | Z=1 |
|     | `MOV B, equal` | | |
|     | `JZ B` | | Should jump (opcode 36) |
|     | `MOV C, 1` | | |
|     | `equal: HLT` | C=0 | Jump taken |
| 201 | `MOV A, 5` | | |
|     | `CMP A, 3` | | Z=0 |
|     | `MOV B, notzero` | | |
|     | `JNZ B` | | Should jump (opcode 38) |
|     | `MOV C, 1` | | |
|     | `notzero: HLT` | C=0 | Jump taken |
| 202 | `MOV A, 200` | | |
|     | `ADD A, 100` | | C=1 |
|     | `MOV B, carry` | | |
|     | `JC B` | | Should jump (opcode 32) |
|     | `MOV C, 1` | | |
|     | `carry: HLT` | C=0 | Jump taken |
| 203 | `MOV A, 5` | | |
|     | `ADD A, 3` | | C=0 |
|     | `MOV B, nocarry` | | |
|     | `JNC B` | | Should jump (opcode 34) |
|     | `MOV C, 1` | | |
|     | `nocarry: HLT` | C=0 | Jump taken |
| 204 | `MOV A, 10` | | |
|     | `CMP A, 3` | | C=0, Z=0 |
|     | `MOV B, above` | | |
|     | `JA B` | | Should jump (opcode 40) |
|     | `MOV C, 1` | | |
|     | `above: HLT` | C=0 | Jump taken |
| 205 | `MOV A, 3` | | |
|     | `CMP A, 10` | | C=1 |
|     | `MOV B, notabove` | | |
|     | `JNA B` | | Should jump (opcode 42) |
|     | `MOV C, 1` | | |
|     | `notabove: HLT` | C=0 | Jump taken |

### 6.24.3 Bitwise — All Addressing Modes

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 206 | `MOV A, 0xFF` | | |
|     | `MOV B, 0x0F` | | |
|     | `AND A, B` | A=0x0F, C=false | AND reg, reg (opcode 70) |
|     | `HLT` | | |
| 207 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 0x0F` | | |
|     | `MOV A, 0xFF` | | |
|     | `AND A, [B]` | A=0x0F, C=false | AND reg, [reg] (opcode 71) |
|     | `HLT` | | |
| 208 | `MOV [0x50], 0x0F` | | |
|     | `MOV A, 0xFF` | | |
|     | `AND A, [0x50]` | A=0x0F, C=false | AND reg, [addr] (opcode 72) |
|     | `HLT` | | |
| 209 | `MOV A, 0xF0` | | |
|     | `MOV B, 0x0F` | | |
|     | `OR A, B` | A=0xFF, C=false | OR reg, reg (opcode 74) |
|     | `HLT` | | |
| 210 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 0x0F` | | |
|     | `MOV A, 0xF0` | | |
|     | `OR A, [B]` | A=0xFF, C=false | OR reg, [reg] (opcode 75) |
|     | `HLT` | | |
| 211 | `MOV [0x50], 0x0F` | | |
|     | `MOV A, 0xF0` | | |
|     | `OR A, [0x50]` | A=0xFF, C=false | OR reg, [addr] (opcode 76) |
|     | `HLT` | | |
| 212 | `MOV A, 0xFF` | | |
|     | `MOV B, 0xFF` | | |
|     | `XOR A, B` | A=0, Z=true, C=false | XOR reg, reg (opcode 78) |
|     | `HLT` | | |
| 213 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 0xFF` | | |
|     | `MOV A, 0xFF` | | |
|     | `XOR A, [B]` | A=0, Z=true, C=false | XOR reg, [reg] (opcode 79) |
|     | `HLT` | | |
| 214 | `MOV [0x50], 0xFF` | | |
|     | `MOV A, 0xFF` | | |
|     | `XOR A, [0x50]` | A=0, Z=true, C=false | XOR reg, [addr] (opcode 80) |
|     | `HLT` | | |

### 6.24.4 Shift — All Addressing Modes

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 215 | `MOV A, 1` | | |
|     | `MOV B, 3` | | |
|     | `SHL A, B` | A=8 | SHL reg, reg (opcode 90) |
|     | `HLT` | | |
| 216 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 2` | | |
|     | `MOV A, 1` | | |
|     | `SHL A, [B]` | A=4 | SHL reg, [reg] (opcode 91) |
|     | `HLT` | | |
| 217 | `MOV [0x50], 3` | | |
|     | `MOV A, 1` | | |
|     | `SHL A, [0x50]` | A=8 | SHL reg, [addr] (opcode 92) |
|     | `HLT` | | |
| 218 | `MOV A, 128` | | |
|     | `MOV B, 1` | | |
|     | `SHR A, B` | A=64 | SHR reg, reg (opcode 94) |
|     | `HLT` | | |
| 219 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 2` | | |
|     | `MOV A, 128` | | |
|     | `SHR A, [B]` | A=32 | SHR reg, [reg] (opcode 95) |
|     | `HLT` | | |
| 220 | `MOV [0x50], 3` | | |
|     | `MOV A, 128` | | |
|     | `SHR A, [0x50]` | A=16 | SHR reg, [addr] (opcode 96) |
|     | `HLT` | | |

### 6.24.5 MOV + DP Forms

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 221 | `MOV A, 5` | | |
|     | `MOV DP, A` | DP=5 | MOV DP, reg (opcode 1, dest=5) |
|     | `HLT` | | |
| 222 | `MOV [0x50], 3` | | |
|     | `MOV DP, [0x50]` | DP=3 | MOV DP, [addr] (opcode 2, dest=5) |
|     | `HLT` | | |
| 223 | `MOV B, 0x50` | | |
|     | `MOV [0x50], 7` | | |
|     | `MOV DP, [B]` | DP=7 | MOV DP, [reg] (opcode 3, dest=5) |
|     | `HLT` | | |
| 224 | `MOV DP, 42` | | |
|     | `MOV [0x50], DP` | mem[0x2A50]=42 | MOV [addr], DP (opcode 4, src=5); DP=42 → page 42 |
|     | `HLT` | | |
| 225 | `MOV DP, 42` | | |
|     | `MOV B, 0x50` | | |
|     | `MOV [B], DP` | mem[0x2A50]=42 | MOV [reg], DP (opcode 5, src=5); DP=42 → page 42 |
|     | `HLT` | | |

### 6.24.6 Flag Preservation — SP/DP MOV

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 226 | `MOV A, 255` | | |
|     | `ADD A, 1` | | C=true, Z=true |
|     | `MOV SP, 200` | C=true, Z=true | MOV to SP preserves flags |
|     | `HLT` | | |
| 227 | `MOV A, 255` | | |
|     | `ADD A, 1` | | C=true, Z=true |
|     | `MOV DP, 5` | C=true, Z=true | MOV to DP preserves flags |
|     | `HLT` | | |

### 6.24.7 Initial Memory Zero

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 228 | `MOV A, [0x50]` | A=0 | Uninitialized memory reads as 0 |
|     | `HLT` | | |

### 6.24.8 Assembler Edge Cases

| # | Source | Expected | Description |
|---|--------|----------|-------------|
| 229 | `a:` | label `a`=0, label `b`=0 | Multiple labels on same address |
|     | `b: HLT` | Bytes: `[0]` | |
| 230 | `DB ""` | error, line: 1 | Empty string in DB |
| 231 | `DB "A", 66` | error, line: 1 | Mixed string + numeric in DB |

---

## 6.25 Test Summary

FP tests (FMOV, FP arithmetic, special values, compare, unary, conversions, control registers, exception model, format faults, flag isolation, cost model, assembler encoding, and IEEE 754 arithmetic validation vectors) are in the separate [FP Test Specification](tests-fp.md).

| Group | Tests | Coverage |
|-------|-------|----------|
| [MOV](#62-mov--data-movement) | 1-9 | 8 opcodes, flag preservation |
| [ADD/SUB](#63-add--sub--arithmetic) | 10-20 | 8 opcodes, overflow, SP, addressing |
| [INC/DEC](#64-inc--dec) | 21-25 | 2 opcodes, boundaries, SP |
| [CMP](#65-cmp--compare) | 26-29 | 4 opcodes, flag combinations |
| [Jumps](#66-jmp--conditional-jumps) | 30-44 | 14 opcodes, aliases |
| [Stack](#67-stack-operations--push--pop) | 45-51 | 5 opcodes, LIFO, boundaries |
| [CALL/RET](#68-call--ret--subroutines) | 52-56 | 3 opcodes, nesting, return addr |
| [MUL/DIV](#69-mul--div) | 57-66 | 8 opcodes, all addressing modes, div/0 |
| [Bitwise](#610-bitwise--and--or--xor--not) | 67-72 | 13 opcodes, C=0, edge cases |
| [Shift](#611-shift--shl--shr) | 73-80 | 8 opcodes, aliases, shift-by-0 |
| [Addressing](#612-addressing-modes) | 81-84 | Offset encoding, SP-relative |
| [Flags](#613-flag-behavior) | 85-89 | Arithmetic flag corner cases |
| [SP restrictions](#614-sp-operand-restrictions) | 90-105 | Allowed/rejected SP usage |
| [I/O](#615-memory-mapped-io) | 106-109 | Display read/write, DP=0 required |
| [Encoding](#616-assembler--encoding) | 110-131 | Bytecode, numbers, labels |
| [Errors](#617-assembler--error-handling) | 132-148 | All 12 error types, line numbers |
| [Mapping](#618-assembler--source-mapping) | 149-151 | Position → line mapping |
| [Integration](#619-integration--end-to-end-programs) | 152-156 | Full programs |
| [Faults & edge cases](#620-fault-conditions-and-edge-cases) | 157-160 | Invalid opcode, address bounds, SP source |
| [DP register](#621-dp-register--paged-memory-access) | 161-170 | Paged memory (64KB), SP-relative, direct+DP |
| [Robustness](#622-robustness-tests-adversarial-scenarios) | 171-181 | Self-mod, stack attacks, invalid opcodes/regs |
| [DB list](#6228-db-comma-separated-list) | 182-184 | Comma-separated DB operands |
| [Coverage](#623-coverage-completeness) | 185-197 | Fetch boundary, DP reject, DIV carry, shift>=8, CMP/SUB modes, CALL/RET faults, wrapping, MUL C+Z, PUSH+DP, I/O exec |
| [Opcode coverage](#624-opcode-coverage-completeness) | 198-231 | SUB/CMP [reg], Jcc reg, AND/OR/XOR all modes, SHL/SHR all modes, MOV+DP forms, SP/DP flag preservation, initial memory, asm edge cases |
| **Total** | **231** | **Integer tests only. FP tests: [tests-fp.md](tests-fp.md)** |
