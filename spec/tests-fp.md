# 8. FP Test Specification

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [Assembler](asm.md), [Microarchitecture](uarch.md), [FPU](fp.md), [Integer Tests](tests.md)

## 8.1 Test Methodology

Each test follows the pattern: **assemble** source code, **execute** until HLT or fault, **verify** CPU state.

FP-specific verification targets:

| Target | Description |
|--------|-------------|
| `FA` | Full 32-bit FP register value (hex) |
| `FHA`, `FHB` | 16-bit FP sub-register values (hex) |
| `FPCR` | FP control register (rounding mode) |
| `FPSR` | FP status register (sticky exception flags) |
| `FPSR.NV` | Invalid operation flag |
| `FPSR.DZ` | Division by zero flag |
| `FPSR.OF` | Overflow flag |
| `FPSR.UF` | Underflow flag |
| `FPSR.NX` | Inexact flag |
| `Z`, `C` | Integer flags (set by FCMP) |
| `F` | Fault flag (true/false) |
| `A` | Error code (on FAULT) |
| `mem[addr]` | Memory byte at address |
| `cost` | Cycle cost of instruction |

FP tests exercise: FP load/store (FMOV), arithmetic (FADD/FSUB/FMUL/FDIV), compare (FCMP), unary (FABS/FNEG/FSQRT), register-to-register arithmetic (FADD_RR/FSUB_RR/FMUL_RR/FDIV_RR/FCMP_RR), classification (FCLASS), fused multiply-add (FMADD), conversions (FCVT/FITOF/FFTOI), control (FSTAT/FCFG/FSCFG/FCLR), exception model, format faults, flag isolation, cost model, and assembler encoding.

**Test numbering:** Tests 1-96 cover the initial FP feature set. Tests 97-121 cover assembler encoding. Tests 122-151 were added for reg-reg operations, FCLASS, FMADD, and additional cost/encoding verification — they are appended to their respective topical sections to preserve logical grouping. Tests 152-160 cover OFP8 (E4M3, E5M2) format support.

**Float data setup pattern:** Tests use `DB` float literals (see [Assembler §5.6](asm.md#db-float-literals)) to initialize float values in memory. Data is placed after `HLT` with forward-referenced labels:

```asm
FMOV.F FA, [one]    ; load float32 from label
FADD.F FA, [two]    ; use float32 from label as memory operand
HLT
one: DB 1.0          ; float32 1.0 (4 bytes LE)
two: DB 2.0          ; float32 2.0 (4 bytes LE)
```

---

## 8.2 FMOV -- FP Load / Store

Tests opcodes 128-131. FMOV must **not** affect flags.

### 8.2.1 Basic Load/Store (float32)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 1 | `FMOV.F FA, [d]` | FA = 0x3F800000 | Load float32 from memory |
|   | `HLT` | | |
|   | `d: DB 1.0` | | float32 1.0 (4 bytes LE) |
| 2 | `FMOV.F FA, [d]` | | Load 1.0 into FA |
|   | `FMOV.F [0x60], FA` | mem[0x60..0x63] = 00,00,80,3F | Store float32 to memory (LE) |
|   | `HLT` | | |
|   | `d: DB 1.0` | | |

### 8.2.2 Basic Load/Store (float16)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 3 | `FMOV.H FHA, [d]` | FHA = 0x3C00 | Load float16 into FHA |
|   | `HLT` | | |
|   | `d: DB 1.0_h` | | float16 1.0 (2 bytes LE) |
| 4 | `FMOV.H FHB, [d]` | FHB = 0x3C00 | Load float16 into FHB |
|   | `HLT` | | |
|   | `d: DB 1.0_h` | | |

### 8.2.3 Basic Load/Store (bfloat16)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 5 | `FMOV.BF FHA, [d]` | FHA = 0x3F80 | Load bfloat16 into FHA |
|   | `HLT` | | |
|   | `d: DB 1.0_bf` | | bfloat16 1.0 (2 bytes LE) |

### 8.2.4 Register Indirect Addressing

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 6 | `MOV B, d` | | B = address of data |
|   | `FMOV.F FA, [B]` | FA = 0x3F800000 | Load float32 via register indirect |
|   | `HLT` | | |
|   | `d: DB 1.0` | | |
| 7 | `FMOV.F FA, [d]` | | Load 1.0 into FA |
|   | `MOV B, 0x60` | | |
|   | `FMOV.F [B], FA` | mem[0x60..0x63] = 00,00,80,3F | Store float32 via register indirect (LE) |
|   | `HLT` | | |
|   | `d: DB 1.0` | | |

### 8.2.5 DP-Aware Access

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 8 | `MOV DP, 1` | | Page 1 |
|   | `FMOV.H FHA, [0x50]` | FHA = mem[0x150..0x151] | Loads from page 1 (abs addr 0x150) |
|   | `MOV DP, 0` | | |
|   | `FMOV.H [0x60], FHA` | mem[0x60..0x61] = mem[0x150..0x151] | Stores to page 0 (abs addr 0x60) |
|   | `HLT` | | |

### 8.2.6 Page Boundary Violation

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 9 | `FMOV.F FA, [253]` | F=true, A=5 | float32 at addr 253: 253+3=256 > 255 |
|   | | state=FAULT | ERR_PAGE_BOUNDARY |
| 10 | `FMOV.H FHA, [255]` | F=true, A=5 | float16 at addr 255: 255+1=256 > 255 |
|    | | state=FAULT | ERR_PAGE_BOUNDARY |

### 8.2.7 Aliasing

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 11 | `FMOV.F FA, [d]` | FA = 0x3F800000 | Load into full register |
|    | `FMOV.H [0x60], FHA` | mem[0x60..0x61] = 00,00 | FHA = low 16 bits (0x0000) |
|    | `FMOV.H [0x62], FHB` | mem[0x62..0x63] = 80,3F | FHB = high 16 bits (0x3F80) |
|    | `HLT` | | Aliased read: raw bits, no conversion |
|    | `d: DB 1.0` | | float32 1.0 = 0x3F800000 |
| 12 | `FMOV.F FA, [d32]` | | FA = 0x3F800000 |
|    | `FMOV.H FHA, [d16]` | | Write float16 to FHA (low 16 bits) |
|    | `FMOV.F [0x70], FA` | mem[0x70..0x71] = 00,3C | FHA = 0x3C00 (written above) |
|    | | mem[0x72..0x73] = 80,3F | FHB unchanged (still high 16 bits of 0x3F800000) |
|    | `HLT` | | Writing FHA doesn't affect FHB |
|    | `d32: DB 1.0` | | float32 1.0 |
|    | `d16: DB 1.0_h` | | float16 1.0 |

### 8.2.8 Flag Preservation

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 13 | `MOV A, 255` | | |
|    | `ADD A, 1` | | C=true, Z=true |
|    | `FMOV.F FA, [d]` | C=true, Z=true | FMOV must not affect flags |
|    | `HLT` | | |
|    | `d: DB 0.0` | | |

---

## 8.3 FP Arithmetic

Tests FADD (132-133), FSUB (134-135), FMUL (136-137), FDIV (138-139).

### 8.3.1 Basic Operations (float32)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 14 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FADD.F FA, [d2]` | FA = 3.0 | 1.0 + 2.0 = 3.0 |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 2.0` | | |
| 15 | `FMOV.F FA, [d1]` | | FA = 5.0 |
|    | `FSUB.F FA, [d2]` | FA = 3.0 | 5.0 - 2.0 = 3.0 |
|    | `HLT` | | |
|    | `d1: DB 5.0` | | |
|    | `d2: DB 2.0` | | |
| 16 | `FMOV.F FA, [d1]` | | FA = 3.0 |
|    | `FMUL.F FA, [d2]` | FA = 12.0 | 3.0 x 4.0 = 12.0 |
|    | `HLT` | | |
|    | `d1: DB 3.0` | | |
|    | `d2: DB 4.0` | | |
| 17 | `FMOV.F FA, [d1]` | | FA = 10.0 |
|    | `FDIV.F FA, [d2]` | FA = 2.5 | 10.0 / 4.0 = 2.5 |
|    | `HLT` | | |
|    | `d1: DB 10.0` | | |
|    | `d2: DB 4.0` | | |

### 8.3.2 Basic Operations (float16)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 18 | `FMOV.H FHA, [d1]` | | FHA = 1.0 (H) |
|    | `FADD.H FHA, [d2]` | FHA = 3.0 (H) | float16 addition |
|    | `HLT` | | |
|    | `d1: DB 1.0_h` | | |
|    | `d2: DB 2.0_h` | | |
| 19 | `FMOV.H FHA, [d1]` | | FHA = 6.0 (H) |
|    | `FDIV.H FHA, [d2]` | FHA = 2.0 (H) | float16 division |
|    | `HLT` | | |
|    | `d1: DB 6.0_h` | | |
|    | `d2: DB 3.0_h` | | |

### 8.3.3 Basic Operations (bfloat16)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 20 | `FMOV.BF FHA, [d1]` | | FHA = 1.0 (BF) |
|    | `FADD.BF FHA, [d2]` | FHA = 3.0 (BF) | bfloat16 addition |
|    | `HLT` | | |
|    | `d1: DB 1.0_bf` | | |
|    | `d2: DB 2.0_bf` | | |
| 21 | `FMOV.BF FHA, [d1]` | | FHA = 4.0 (BF) |
|    | `FMUL.BF FHA, [d2]` | FHA = 8.0 (BF) | bfloat16 multiplication |
|    | `HLT` | | |
|    | `d1: DB 4.0_bf` | | |
|    | `d2: DB 2.0_bf` | | |

### 8.3.4 Register Indirect (float32)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 22 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `MOV B, d2` | | B = address of 2.0 |
|    | `FADD.F FA, [B]` | FA = 3.0 | FADD via register indirect |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 2.0` | | |

### 8.3.5 Register-to-Register Operations

Tests opcodes 153-156 (FADD_RR, FSUB_RR, FMUL_RR, FDIV_RR).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 122 | `FMOV.F FA, [d]` | | FA = 1.0 |
|     | `FADD.F FA, FA` | FA = 2.0 | float32 self-add: 1.0 + 1.0 |
|     | `HLT` | | |
|     | `d: DB 1.0` | | |
| 123 | `FMOV.H FHA, [d1]` | | FHA = 3.0 (H) |
|     | `FMOV.H FHB, [d2]` | | FHB = 2.0 (H) |
|     | `FSUB.H FHA, FHB` | FHA = 1.0 (H) | float16 cross-position |
|     | `HLT` | | |
|     | `d1: DB 3.0_h` | | |
|     | `d2: DB 2.0_h` | | |
| 124 | `FMOV.F FA, [d]` | | FA = 3.0 |
|     | `FMUL.F FA, FA` | FA = 9.0 | float32 self-mul: 3.0 × 3.0 |
|     | `HLT` | | |
|     | `d: DB 3.0` | | |
| 125 | `FMOV.H FHA, [d1]` | | FHA = 6.0 (H) |
|     | `FMOV.H FHB, [d2]` | | FHB = 2.0 (H) |
|     | `FDIV.H FHA, FHB` | FHA = 3.0 (H) | float16 cross-position |
|     | `HLT` | | |
|     | `d1: DB 6.0_h` | | |
|     | `d2: DB 2.0_h` | | |
| 126 | `FMOV.BF FHA, [d1]` | | FHA = 1.0 (BF) |
|     | `FMOV.BF FHB, [d2]` | | FHB = 2.0 (BF) |
|     | `FADD.BF FHA, FHB` | FHA = 3.0 (BF) | bfloat16 reg-reg |
|     | `HLT` | | |
|     | `d1: DB 1.0_bf` | | |
|     | `d2: DB 2.0_bf` | | |

### 8.3.6 Register-to-Register Format Fault

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 127 | `DB 153, 0x00, 0x01` | F=true, A=12 | FADD_RR: dst=FA(.F), src=FHA(.H) → fmt mismatch |
|     | | state=FAULT | ERR_FP_FORMAT |

### 8.3.7 Fused Multiply-Add (FMADD)

Tests opcodes 159-160. FMADD computes `dst = src × mem + dst`. First 4-byte instruction.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 128 | `FMOV.F FA, [d1]` | | FA = 2.0 (accumulator) |
|     | `FMADD.F FA, FA, [d2]` | FA = 8.0 | FA = FA × mem + FA = 2.0 × 3.0 + 2.0 |
|     | `HLT` | | |
|     | `d1: DB 2.0` | | |
|     | `d2: DB 3.0` | | |
| 129 | `FMOV.H FHA, [d1]` | | FHA = 1.0 (H, accumulator) |
|     | `FMOV.H FHB, [d2]` | | FHB = 2.0 (H, multiplier) |
|     | `FMADD.H FHA, FHB, [d3]` | FHA = 7.0 (H) | FHA = FHB × mem + FHA = 2.0 × 3.0 + 1.0 |
|     | `HLT` | | |
|     | `d1: DB 1.0_h` | | |
|     | `d2: DB 2.0_h` | | |
|     | `d3: DB 3.0_h` | | |
| 130 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|     | `MOV B, d2` | | B = address of 3.0 |
|     | `FMADD.F FA, FA, [B]` | FA = 4.0 | FMADD indirect: 1.0 × 3.0 + 1.0 |
|     | `HLT` | | |
|     | `d1: DB 1.0` | | |
|     | `d2: DB 3.0` | | |

### 8.3.8 FMADD Faults

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 131 | `DB 159, 0x00, 0x01, 0x50` | F=true, A=12 | FMADD: dst=FA(.F), src=FHA(.H) → fmt mismatch |
|     | | state=FAULT | ERR_FP_FORMAT |
| 132 | (IP=253) `DB 159, 0x00, 0x00, 0x50` | F=true, A=5 | 4-byte instruction at IP 253: 253+4=257 >= 256 |
|     | | state=FAULT | ERR_PAGE_BOUNDARY |

---

## 8.4 FP Special Values

Tests IEEE 754 special value handling.

### 8.4.1 Infinity Arithmetic

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 23 | `FMOV.F FA, [d1]` | | FA = +Inf |
|    | `FADD.F FA, [d2]` | FA = +Inf | Inf + finite = Inf |
|    | `HLT` | | |
|    | `d1: DB inf` | | |
|    | `d2: DB 1.0` | | |
| 24 | `FMOV.F FA, [d1]` | | FA = +Inf |
|    | `FADD.F FA, [d2]` | FA = +Inf | Inf + Inf = Inf |
|    | `HLT` | | |
|    | `d1: DB inf` | | |
|    | `d2: DB inf` | | |
| 25 | `FMOV.F FA, [d1]` | | FA = +Inf |
|    | `FSUB.F FA, [d2]` | FA = NaN, FPSR.NV=1 | Inf - Inf = NaN (Invalid) |
|    | `HLT` | | |
|    | `d1: DB inf` | | |
|    | `d2: DB inf` | | |

### 8.4.2 NaN Propagation

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 26 | `FMOV.F FA, [d1]` | | FA = qNaN |
|    | `FADD.F FA, [d2]` | FA = qNaN | NaN + finite = NaN |
|    | `HLT` | | |
|    | `d1: DB nan` | | |
|    | `d2: DB 1.0` | | |
| 27 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FMUL.F FA, [d2]` | FA = qNaN | finite x NaN = NaN |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB nan` | | |

### 8.4.3 Denormals

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 28 | `FMOV.F FA, [d1]` | | FA = smallest denorm |
|    | `FADD.F FA, [d2]` | FA = smallest denorm | denorm + 0.0 = denorm |
|    | `HLT` | | |
|    | `d1: DB 1.4e-45` | | smallest float32 denorm (0x00000001) |
|    | `d2: DB 0.0` | | |

### 8.4.4 Signed Zero

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 29 | `FMOV.F FA, [d1]` | | FA = -0.0 |
|    | `FCMP.F FA, [d2]` | Z=1, C=0 | -0.0 == +0.0 |
|    | `HLT` | | |
|    | `d1: DB -0.0` | | |
|    | `d2: DB 0.0` | | |

---

## 8.5 FP Compare

Tests FCMP (140-141) flag mapping.

### 8.5.1 Basic Comparisons

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 30 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FCMP.F FA, [d2]` | Z=1, C=0 | Equal |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 1.0` | | |
| 31 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FCMP.F FA, [d2]` | Z=0, C=1 | Less than |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 2.0` | | |
| 32 | `FMOV.F FA, [d1]` | | FA = 3.0 |
|    | `FCMP.F FA, [d2]` | Z=0, C=0 | Greater than |
|    | `HLT` | | |
|    | `d1: DB 3.0` | | |
|    | `d2: DB 1.0` | | |

### 8.5.2 Unordered (NaN)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 33 | `FMOV.F FA, [d1]` | | FA = qNaN |
|    | `FCMP.F FA, [d2]` | Z=1, C=1 | Unordered (NaN) |
|    | `HLT` | | |
|    | `d1: DB nan` | | |
|    | `d2: DB 1.0` | | |

### 8.5.3 Jcc Integration

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 34 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FCMP.F FA, [d2]` | | FA < mem -> C=1 |
|    | `JC less` | | Should jump |
|    | `MOV B, 1` | | |
|    | `less: HLT` | B=0 | Jump taken (FP less than) |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 2.0` | | |
| 35 | `FMOV.F FA, [d1]` | | FA = 3.0 |
|    | `FCMP.F FA, [d2]` | | FA > mem -> C=0, Z=0 |
|    | `JA greater` | | Should jump |
|    | `MOV B, 1` | | |
|    | `greater: HLT` | B=0 | Jump taken (FP greater than) |
|    | `d1: DB 3.0` | | |
|    | `d2: DB 1.0` | | |
| 36 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FCMP.F FA, [d2]` | | FA == mem -> Z=1 |
|    | `JZ equal` | | Should jump |
|    | `MOV B, 1` | | |
|    | `equal: HLT` | B=0 | Jump taken (FP equal) |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 1.0` | | |

### 8.5.4 float16 Compare

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 37 | `FMOV.H FHA, [d1]` | | FHA = 1.0 (H) |
|    | `FCMP.H FHA, [d2]` | Z=0, C=1 | float16 less than |
|    | `HLT` | | |
|    | `d1: DB 1.0_h` | | |
|    | `d2: DB 2.0_h` | | |

### 8.5.5 Register-to-Register Compare

Tests opcode 157 (FCMP_RR). Same flag mapping as memory FCMP.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 133 | `FMOV.F FA, [d]` | | FA = 1.0 |
|     | `FCMP.F FA, FA` | Z=1, C=0 | Self-compare: equal |
|     | `HLT` | | |
|     | `d: DB 1.0` | | |
| 134 | `FMOV.H FHA, [d1]` | | FHA = 1.0 (H) |
|     | `FMOV.H FHB, [d2]` | | FHB = 2.0 (H) |
|     | `FCMP.H FHA, FHB` | Z=0, C=1 | Less than |
|     | `HLT` | | |
|     | `d1: DB 1.0_h` | | |
|     | `d2: DB 2.0_h` | | |
| 135 | `FMOV.H FHA, [d1]` | | FHA = 5.0 (H) |
|     | `FMOV.H FHB, [d2]` | | FHB = 2.0 (H) |
|     | `FCMP.H FHA, FHB` | Z=0, C=0 | Greater than |
|     | `HLT` | | |
|     | `d1: DB 5.0_h` | | |
|     | `d2: DB 2.0_h` | | |
| 136 | `FMOV.H FHA, [d1]` | | FHA = 1.0 (H) |
|     | `FMOV.H FHB, [d2]` | | FHB = 1.0 (H) |
|     | `FCMP.H FHA, FHB` | | Equal → Z=1 |
|     | `JZ eq` | | Should jump |
|     | `MOV B, 1` | | |
|     | `eq: HLT` | B=0 | Jump taken (FCMP_RR + JZ) |
|     | `d1: DB 1.0_h` | | |
|     | `d2: DB 1.0_h` | | |

---

## 8.6 FP Unary Operations

Tests FABS (142), FNEG (143), FSQRT (144).

### 8.6.1 FABS

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 38 | `FMOV.F FA, [d]` | | FA = -3.0 |
|    | `FABS.F FA` | FA = 3.0 | Absolute value of negative |
|    | `HLT` | | |
|    | `d: DB -3.0` | | |
| 39 | `FMOV.F FA, [d]` | | FA = 5.0 |
|    | `FABS.F FA` | FA = 5.0 | Absolute value of positive (unchanged) |
|    | `HLT` | | |
|    | `d: DB 5.0` | | |

### 8.6.2 FNEG

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 40 | `FMOV.F FA, [d]` | | FA = 3.0 |
|    | `FNEG.F FA` | FA = -3.0 | Negate positive |
|    | `HLT` | | |
|    | `d: DB 3.0` | | |
| 41 | `FMOV.F FA, [d]` | | FA = -3.0 |
|    | `FNEG.F FA` | FA = 3.0 | Negate negative |
|    | `HLT` | | |
|    | `d: DB -3.0` | | |
| 42 | `FMOV.F FA, [d]` | | FA = +0.0 |
|    | `FNEG.F FA` | FA = -0.0 | Negate zero flips sign bit |
|    | `HLT` | | |
|    | `d: DB 0.0` | | |

### 8.6.3 FSQRT

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 43 | `FMOV.F FA, [d]` | | FA = 4.0 |
|    | `FSQRT.F FA` | FA = 2.0 | sqrt(4) = 2 |
|    | `HLT` | | |
|    | `d: DB 4.0` | | |
| 44 | `FMOV.F FA, [d]` | | FA = 0.0 |
|    | `FSQRT.F FA` | FA = 0.0 | sqrt(0) = 0 |
|    | `HLT` | | |
|    | `d: DB 0.0` | | |
| 45 | `FMOV.F FA, [d]` | | FA = -1.0 |
|    | `FSQRT.F FA` | FA = NaN, FPSR.NV=1 | sqrt(negative) -> Invalid |
|    | `HLT` | | |
|    | `d: DB -1.0` | | |
| 46 | `FMOV.F FA, [d]` | | FA = +Inf |
|    | `FSQRT.F FA` | FA = +Inf | sqrt(+Inf) = +Inf |
|    | `HLT` | | |
|    | `d: DB inf` | | |
| 47 | `FMOV.F FA, [d]` | | FA = qNaN |
|    | `FSQRT.F FA` | FA = NaN | sqrt(NaN) = NaN |
|    | `HLT` | | |
|    | `d: DB nan` | | |
| 48 | `FMOV.H FHA, [d]` | | FHA = 4.0 (H) |
|    | `FSQRT.H FHA` | FHA = 2.0 (H) | float16 FSQRT |
|    | `HLT` | | |
|    | `d: DB 4.0_h` | | |

### 8.6.4 Unary on float16/bfloat16

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 49 | `FMOV.H FHA, [d]` | | FHA = -2.0 (H) |
|    | `FABS.H FHA` | FHA = 2.0 (H) | FABS on float16 |
|    | `HLT` | | |
|    | `d: DB -2.0_h` | | |
| 50 | `FMOV.BF FHA, [d]` | | FHA = 3.0 (BF) |
|    | `FNEG.BF FHA` | FHA = -3.0 (BF) | FNEG on bfloat16 |
|    | `HLT` | | |
|    | `d: DB 3.0_bf` | | |

### 8.6.5 FCLASS — FP Classification

Tests opcode 158. Writes classification bitmask to GPR.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 137 | `FMOV.F FA, [d]` | | FA = +0.0 |
|     | `FCLASS.F A, FA` | A=0x01 | +0.0 → ZERO (bit 0) |
|     | `HLT` | | |
|     | `d: DB 0.0` | | |
| 138 | `FMOV.F FA, [d]` | | FA = -0.0 |
|     | `FCLASS.F A, FA` | A=0x41 | -0.0 → ZERO\|NEG (bits 0+6) |
|     | `HLT` | | |
|     | `d: DB -0.0` | | |
| 139 | `FMOV.F FA, [d]` | | FA = +Inf |
|     | `FCLASS.F A, FA` | A=0x08 | +Inf → INF (bit 3) |
|     | `HLT` | | |
|     | `d: DB inf` | | |
| 140 | `FMOV.F FA, [d]` | | FA = qNaN |
|     | `FCLASS.F A, FA` | A=0x10 | qNaN → NAN (bit 4) |
|     | `HLT` | | |
|     | `d: DB nan` | | |
| 141 | `FMOV.F FA, [d]` | | FA = 1.0 (positive normal) |
|     | `FCLASS.F A, FA` | A=0x04 | +normal → NORM (bit 2) |
|     | `HLT` | | |
|     | `d: DB 1.0` | | |
| 142 | `FMOV.H FHA, [d]` | | FHA = +0.0 (H) |
|     | `FCLASS.H B, FHA` | B=0x01 | float16 classification |
|     | `HLT` | | |
|     | `d: DB 0.0_h` | | |

### 8.6.6 FCLASS Faults

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 143 | `DB 158, 0x00, 4` | F=true, A=4 | FCLASS with SP (gpr=4) → ERR_INVALID_REG |
|     | | state=FAULT | |
| 144 | `DB 158, 0x07, 0` | F=true, A=12 | FCLASS with fmt=7 (reserved) → ERR_FP_FORMAT |
|     | | state=FAULT | |

---

## 8.7 FP Conversions

Tests FCVT (146), FITOF (147), FFTOI (148).

### 8.7.1 FCVT -- Format Conversion

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 51 | `FMOV.F FA, [d]` | | FA = 1.5 (float32) |
|    | `FCVT.H.F FHA, FA` | FHA = 1.5 (float16) | float32 -> float16 (exact) |
|    | `HLT` | | |
|    | `d: DB 1.5` | | |
| 52 | `FMOV.H FHA, [d]` | | FHA = 2.0 (float16) |
|    | `FCVT.F.H FA, FHA` | FA = 2.0 (float32) | float16 -> float32 (exact) |
|    | `HLT` | | |
|    | `d: DB 2.0_h` | | |
| 53 | `FMOV.F FA, [d]` | | FA = 1.0 (float32) |
|    | `FCVT.BF.F FHB, FA` | FHB = 1.0 (bfloat16) | float32 -> bfloat16 |
|    | `HLT` | | |
|    | `d: DB 1.0` | | |
| 54 | `FMOV.H FHA, [d]` | | FHA = 0.5 (float16) |
|    | `FCVT.BF.H FHB, FHA` | FHB = 0.5 (bfloat16) | float16 -> bfloat16 |
|    | `HLT` | | |
|    | `d: DB 0.5_h` | | |

### 8.7.2 FITOF -- Integer to FP

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 55 | `MOV A, 42` | | |
|    | `FITOF.F FA, A` | FA = 42.0 (float32) | uint8 -> float32 |
|    | `HLT` | | |
| 56 | `MOV A, 0` | | |
|    | `FITOF.F FA, A` | FA = 0.0 (float32) | uint8 zero -> float32 |
|    | `HLT` | | |
| 57 | `MOV A, 255` | | |
|    | `FITOF.F FA, A` | FA = 255.0 (float32) | uint8 max -> float32 |
|    | `HLT` | | |
| 58 | `MOV A, 100` | | |
|    | `FITOF.H FHA, A` | FHA = 100.0 (float16) | uint8 -> float16 |
|    | `HLT` | | |

### 8.7.3 FFTOI -- FP to Integer (Saturating)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 59 | `FMOV.F FA, [d]` | | |
|    | `FFTOI.F A, FA` | A=42 | float32 42.0 -> uint8 |
|    | `HLT` | | |
|    | `d: DB 42.0` | | |
| 60 | `FMOV.F FA, [d]` | | |
|    | `FFTOI.F A, FA` | A=43 (RNE) | Rounded (RNE: 42.7 -> 43) |
|    | `HLT` | | |
|    | `d: DB 42.7` | | |
| 61 | `FMOV.F FA, [d]` | | |
|    | `FFTOI.F A, FA` | A=255 | Saturate to max uint8 |
|    | `HLT` | | |
|    | `d: DB 300.0` | | |
| 62 | `FMOV.F FA, [d]` | | |
|    | `FFTOI.F A, FA` | A=0 | Saturate to 0 (negative) |
|    | `HLT` | | |
|    | `d: DB -5.0` | | |
| 63 | `FMOV.F FA, [d]` | | |
|    | `FFTOI.F A, FA` | A=255, FPSR.NV=1 | +Inf -> 255, Invalid flag set |
|    | `HLT` | | |
|    | `d: DB inf` | | |
| 64 | `FMOV.F FA, [d]` | | |
|    | `FFTOI.F A, FA` | A=0, FPSR.NV=1 | NaN -> 0, Invalid flag set |
|    | `HLT` | | |
|    | `d: DB nan` | | |

---

## 8.8 FP Control Registers

Tests FSTAT (149), FCFG (150), FSCFG (151), FCLR (152).

### 8.8.1 Read/Write FPCR

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 65 | `FCFG A` | A=0 | FPCR default is 0 |
|    | `HLT` | | |
| 66 | `MOV A, 0x04` | | Bit 2 set (outside RM [1:0]) |
|    | `FSCFG A` | | Set FPCR |
|    | `FCFG B` | B=0x00 | Read back FPCR (bits [7:2] masked to 0) |
|    | `HLT` | | |
| 67 | `MOV A, 0x03` | | RM=11 (RUP) |
|    | `FSCFG A` | | |
|    | `FCFG B` | B=0x03 | Rounding mode set to RUP |
|    | `HLT` | | |
| 68 | `MOV A, 0xFF` | | All bits set (including reserved bits [7:2]) |
|    | `FSCFG A` | | |
|    | `FCFG B` | B=0x03 | Only RM bits [1:0] kept; bits [7:2] masked to 0 |
|    | `HLT` | | |

### 8.8.2 Read/Write FPSR

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 69 | `FSTAT A` | A=0 | FPSR default is 0 |
|    | `HLT` | | |
| 70 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FDIV.F FA, [d2]` | | 1.0 / 3.0 triggers Inexact |
|    | `FSTAT A` | A has NX bit set | FPSR flag sticky |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 3.0` | | |

### 8.8.3 FCLR

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 71 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FDIV.F FA, [d2]` | | 1.0 / 3.0 triggers Inexact |
|    | `FSTAT A` | A != 0 | FPSR has flags set |
|    | `FCLR` | | Clear all flags |
|    | `FSTAT B` | B=0 | FPSR is now 0 |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 3.0` | | |

### 8.8.4 Control Instruction GPR Restriction

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 72 | `DB 149, 4` | F=true, A=4 | FSTAT with SP (code 4) -> ERR_INVALID_REG |
|    | | state=FAULT | |
| 73 | `DB 151, 5` | F=true, A=4 | FSCFG with DP (code 5) -> ERR_INVALID_REG |
|    | | state=FAULT | |

---

## 8.9 FP Exception Model

Tests that FP arithmetic exceptions set FPSR sticky flags and produce IEEE 754 default results. FP arithmetic exceptions never cause FAULT.

### 8.9.1 Exception Flag Behavior

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 74 | `FMOV.F FA, [d]` | | FA = -1.0 |
|    | `FSQRT.F FA` | FA=NaN, FPSR.NV=1 | Invalid: flag set + qNaN result |
|    | `HLT` | state=HALTED | Execution continues |
|    | `d: DB -1.0` | | |
| 75 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FDIV.F FA, [d2]` | FA=+Inf, FPSR.DZ=1 | DivZero: flag set + Inf result |
|    | `HLT` | state=HALTED | Execution continues |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 0.0` | | |
| 76 | `FMOV.F FA, [d1]` | | FA = max float32 |
|    | `FMUL.F FA, [d2]` | FA=+Inf, FPSR.OF=1, FPSR.NX=1 | Overflow: flag set + Inf, Inexact also set |
|    | `HLT` | state=HALTED | |
|    | `d1: DB 3.4028235e+38` | | max finite float32 (0x7F7FFFFF) |
|    | `d2: DB 2.0` | | |
| 77 | `FMOV.F FA, [d1]` | | FA = min normal |
|    | `FDIV.F FA, [d2]` | FA=denorm, FPSR.UF=1 | Underflow: flag set + denorm result |
|    | `HLT` | state=HALTED | |
|    | `d1: DB 1.1754944e-38` | | min normal float32 (0x00800000) |
|    | `d2: DB 2.0` | | |
| 78 | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FDIV.F FA, [d2]` | FA~=0.333..., FPSR.NX=1 | Inexact: flag set + rounded result |
|    | `HLT` | state=HALTED | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 3.0` | | |

### 8.9.2 Sticky Flags Accumulate

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 79 | `FMOV.F FA, [neg1]` | | FA = -1.0 |
|    | `FSQRT.F FA` | | sqrt(-1) -> NaN, sets NV |
|    | `FMOV.F FA, [one]` | | FA = 1.0 |
|    | `FDIV.F FA, [zero]` | | 1.0/0.0 -> Inf, sets DZ |
|    | `FSTAT A` | A has both NV and DZ bits | Sticky = OR'd |
|    | `HLT` | | |
|    | `neg1: DB -1.0` | | |
|    | `one: DB 1.0` | | |
|    | `zero: DB 0.0` | | |

---

## 8.10 FP Format Faults

Tests ERR_FP_FORMAT (code 12) -- always FAULT.

### 8.10.1 Invalid FPM Byte

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 80 | `DB 142, 0x07` | F=true, A=12 | FABS with fmt=7 (reserved) -> FAULT |
|    | | state=FAULT | ERR_FP_FORMAT |
| 81 | `DB 142, 0x80` | F=true, A=12 | FABS with phys=2 (v2: invalid) -> FAULT |
|    | | state=FAULT | ERR_FP_FORMAT |
| 82 | `DB 142, 0x05` | F=true, A=12 | FABS with fmt=5 (.N1, reserved 4-bit in v2) -> FAULT |
|    | | state=FAULT | ERR_FP_FORMAT |

### 8.10.2 Position Out of Range

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 83 | `DB 142, 0x08` | F=true, A=12 | FABS with fmt=0(.F), pos=1 (invalid: .F only pos 0) |
|    | | state=FAULT | ERR_FP_FORMAT |
| 84 | `DB 142, 0x11` | F=true, A=12 | FABS with fmt=1(.H), pos=2 (invalid: .H only pos 0-1) |
|    | | state=FAULT | ERR_FP_FORMAT |

### 8.10.3 Reserved Format Operations

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 85 | `FADD.N1 FOA, [0x50]` | F=true, A=12 | 4-bit format operation -> FAULT in v2 |
|    | | state=FAULT | ERR_FP_FORMAT |
| 86 | `DB 128, 0x05, 0x50` | F=true, A=12 | FMOV with fmt=5 (.N1, reserved 4-bit in v2) -> FAULT |
|    | | state=FAULT | ERR_FP_FORMAT |

---

## 8.11 FP + Integer Flag Isolation

Tests that FP operations and integer operations interact correctly with flags.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 87 | `MOV A, 255` | | |
|    | `ADD A, 1` | C=true, Z=true | Integer sets C, Z |
|    | `FABS.F FA` | C=true, Z=true | FP unary doesn't touch integer flags |
|    | `HLT` | | |
| 88 | `MOV A, 5` | | |
|    | `CMP A, 3` | Z=false, C=false | Integer flags: Z=0, C=0 |
|    | `FMOV.F FA, [d1]` | | FA = 1.0 |
|    | `FCMP.F FA, [d2]` | Z=0, C=1 | FP compare overwrites Z, C |
|    | `HLT` | | |
|    | `d1: DB 1.0` | | |
|    | `d2: DB 2.0` | | |
| 89 | `FMOV.F FA, [d]` | | FA = 1.0 |
|    | `FCMP.F FA, [d]` | Z=1, C=0 | FP equal sets Z=1, C=0 |
|    | `MOV A, 5` | Z=1, C=0 | MOV doesn't change flags |
|    | `ADD A, 0` | Z=0, C=0 | Integer ADD recomputes flags from result |
|    | `HLT` | | |
|    | `d: DB 1.0` | | |

---

## 8.12 FP Cost Model Verification

Tests that FP instructions report correct cycle costs.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 90 | `FABS.F FA` | cost=3 | FP unary cost |
|    | `HLT` | | |
| 91 | `FSQRT.F FA` | cost=4 | FSQRT cost |
|    | `HLT` | | |
| 92 | `FMOV.F FA, [d]` | cost=2 | FP load cost |
|    | `HLT` | | |
|    | `d: DB 0.0` | | |
| 93 | `FADD.F FA, [d]` | cost=5 | FP binary + mem cost |
|    | `HLT` | | |
|    | `d: DB 0.0` | | |
| 94 | `FCLR` | cost=1 | FP control cost |
|    | `HLT` | | |
| 95 | `FCVT.H.F FHA, FA` | cost=3 | FP conversion cost |
|    | `HLT` | | |
| 96 | `FITOF.F FA, A` | cost=3 | Integer-to-FP conversion cost |
|    | `HLT` | | |
| 145 | `FMOV.F FA, [d]` | | FA = 1.0 |
|     | `FADD.F FA, FA` | cost=3 | FP reg-reg cost |
|     | `HLT` | | |
|     | `d: DB 1.0` | | |
| 146 | `FCLASS.F A, FA` | cost=2 | FCLASS cost |
|     | `HLT` | | |
| 147 | `FMOV.F FA, [d]` | | FA = 1.0 |
|     | `FMADD.F FA, FA, [d]` | cost=6 | FMADD cost |
|     | `HLT` | | |
|     | `d: DB 1.0` | | |

---

## 8.13 FP Assembler Encoding Verification

Tests that the assembler produces correct bytecode for FP instructions.

### 8.13.1 FPM Byte Encoding

| # | Source | Expected bytes | Description |
|---|--------|--------------------|-------------|
| 97 | `FABS.F FA` | `[142, 0x00]` | fmt=0, pos=0, phys=0 -> FPM=0x00 |
| 98 | `FABS.H FHA` | `[142, 0x01]` | fmt=1, pos=0 -> FPM=0x01 |
| 99 | `FABS.H FHB` | `[142, 0x09]` | fmt=1, pos=1 -> FPM=0x09 |
| 100 | `FABS.BF FHA` | `[142, 0x02]` | fmt=2, pos=0 -> FPM=0x02 |
| 101 | `FABS.BF FHB` | `[142, 0x0A]` | fmt=2, pos=1 -> FPM=0x0A |

### 8.13.2 Instruction Encoding

| # | Source | Expected bytes | Description |
|---|--------|--------------------|-------------|
| 102 | `FMOV.F FA, [0x50]` | `[128, 0x00, 0x50]` | Load float32 direct |
| 103 | `FMOV.H FHA, [0x50]` | `[128, 0x01, 0x50]` | Load float16 direct |
| 104 | `FMOV.F [0x60], FA` | `[130, 0x00, 0x60]` | Store float32 direct |
| 105 | `FADD.F FA, [0x50]` | `[132, 0x00, 0x50]` | FADD float32 direct |
| 106 | `FCMP.H FHB, [0x50]` | `[140, 0x09, 0x50]` | FCMP float16 FHB direct |
| 107 | `FCVT.H.F FHA, FA` | `[146, 0x01, 0x00]` | FCVT: dst=FHA(.H), src=FA(.F) |
| 108 | `FITOF.F FA, A` | `[147, 0x00, 0x00]` | FITOF: FPM=FA(.F), gpr=A(0) |
| 109 | `FFTOI.F B, FA` | `[148, 0x00, 0x01]` | FFTOI: FPM=FA(.F), gpr=B(1) |
| 110 | `FSTAT A` | `[149, 0x00]` | FSTAT: gpr=A(0) |
| 111 | `FSCFG B` | `[151, 0x01]` | FSCFG: gpr=B(1) |
| 112 | `FCLR` | `[152]` | 1-byte instruction |
| 148 | `FADD.F FA, FA` | `[153, 0x00, 0x00]` | FADD_RR float32 FA,FA |
| 149 | `FCMP.H FHA, FHB` | `[157, 0x01, 0x09]` | FCMP_RR float16 FHA vs FHB |
| 150 | `FCLASS.F A, FA` | `[158, 0x00, 0x00]` | FCLASS: FPM=FA(.F), gpr=A(0) |
| 151 | `FMADD.F FA, FA, [0x50]` | `[159, 0x00, 0x00, 0x50]` | FMADD float32 direct (4 bytes) |

### 8.13.3 EXMY Alias Equivalence

| # | Source | Expected | Description |
|---|--------|----------|-------------|
| 113 | `FADD.F FA, [0x50]` vs `FADD.E8M23 FA, [0x50]` | Same bytes | Short and EXMY produce identical encoding |
| 114 | `FADD.H FHA, [0x50]` vs `FADD.E5M10 FHA, [0x50]` | Same bytes | float16 alias equivalence |
| 115 | `FADD.BF FHA, [0x50]` vs `FADD.E8M7 FHA, [0x50]` | Same bytes | bfloat16 alias equivalence |

### 8.13.4 FP Assembler Errors

| # | Source | Expected Error | Description |
|---|--------|---------------|-------------|
| 116 | `FADD FA, [0x50]` | `FP format suffix required` | Missing suffix |
| 117 | `FADD.F FHA, [0x50]` | `FP format suffix does not match register width` | .F (32-bit) + FHA (16-bit) |
| 118 | `FADD.H FA, [0x50]` | `FP format suffix does not match register width` | .H (16-bit) + FA (32-bit) |
| 119 | `FADD.XYZ FA, [0x50]` | `Invalid FP format suffix: XYZ` | Unknown suffix |
| 120 | `FA: HLT` | `Label contains keyword: FA` | FP register name as label |
| 121 | `FHA: HLT` | `Label contains keyword: FHA` | FP register name as label |

---

## 8.14 IEEE 754 Arithmetic Validation

### 8.14.1 Test Vector Source

Test vectors: [sergev/ieee754-test-suite](https://github.com/sergev/ieee754-test-suite) (IBM FPgen, `.fptest` format).

Only lines with prefix `b32` (binary32 = float32 E8M23) are used. The test suite is located in `ieee754-test-suite/` at the repository root.

### 8.14.2 `.fptest` Format Reference

Each line encodes one test vector:

```
b32+ =0 x +1.7FFFFDP-6 -1.000000P-5 -> +1.400000P-28
|    |  |  |operand1     |operand2      |result
|    |  |  +-- hex mantissa + P + decimal exponent
|    |  +-- expected exceptions (x=inexact, u=underflow, o=overflow, z=divzero, i=invalid)
|    +-- rounding mode (=0:RNE, 0:RTZ, >:RUP, <:RDN)
+-- precision+operation (b32+, b32-, b32*, b32/)
```

Special operand tokens: `+Inf`, `-Inf`, `+Zero`, `-Zero`, `Q` (qNaN), `S` (sNaN).

### 8.14.3 Mapping `.fptest` to sim8

**Operation mapping:**

| `.fptest` prefix | sim8 instruction |
|-----------------|------------------|
| `b32+` | `FADD.F FA, [addr]` |
| `b32-` | `FSUB.F FA, [addr]` |
| `b32*` | `FMUL.F FA, [addr]` |
| `b32/` | `FDIV.F FA, [addr]` |
| `b32>C` | `FCMP.F FA, [addr]` |

**Rounding mode mapping:**

| `.fptest` code | FPCR.RM value | Mode |
|---------------|---------------|------|
| `=0` | 00 | RNE (Round to Nearest, ties to Even) |
| `0` | 01 | RTZ (Round toward Zero) |
| `<` | 10 | RDN (Round toward -Inf) |
| `>` | 11 | RUP (Round toward +Inf) |

**Exception flag mapping:**

| `.fptest` flag | FPSR bit |
|---------------|----------|
| `x` | NX (bit 4) |
| `u` | UF (bit 3) |
| `o` | OF (bit 2) |
| `z` | DZ (bit 1) |
| `i` | NV (bit 0) |

**Note:** The `.fptest` format's "trapped exceptions" field originates from the IBM FPgen test suite which supports trap-based exception handling. sim8 does not support traps — all FP exceptions set FPSR sticky flags. The exception letters are used only to verify which FPSR flags should be set after the operation.

**Execution pattern for each vector:**

```
1. Set FPCR.RM to the specified rounding mode
2. Clear FPSR via FCLR
3. Load operand1 into FA via FMOV.F
4. Store operand2 to memory
5. Execute the mapped instruction (FADD.F / FSUB.F / FMUL.F / FDIV.F)
6. Verify: FA = expected result, FPSR flags match exception flags from the vector
```

### 8.14.4 Relevant `.fptest` Files

| Category | `.fptest` file(s) | sim8 instruction | Rounding | Checked exceptions |
|----------|-------------------|------------------|----------|--------------------|
| Addition (cancellation) | `Add-Cancellation`, `Add-Cancellation-And-Subnorm-Result` | FADD.F | RNE | Inexact, Underflow |
| Addition (shift) | `Add-Shift`, `Add-Shift-And-Special-Significands` | FADD.F | RNE | Inexact, Overflow |
| Subtraction (cancellation) | `Add-Cancellation` (lines `b32-`) | FSUB.F | RNE | Inexact, Underflow |
| Division (basic) | `Divide-Trailing-Zeros` | FDIV.F | RNE | Inexact |
| Division (div-zero) | `Divide-Divide-By-Zero-Exception` | FDIV.F | RNE | DivZero |
| Overflow | `Overflow` | FADD/FSUB/FMUL/FDIV.F | all 4 | Overflow, Inexact |
| Underflow | `Underflow` | FADD/FSUB/FMUL/FDIV.F | all 4 | Underflow, Inexact |
| Rounding | `Rounding`, `Corner-Rounding`, `Vicinity-Of-Rounding-Boundaries` | all arith | all 4 | Inexact |
| Sticky bit | `Sticky-Bit-Calculation` | all arith | RNE | Inexact |
| Compare | `Compare-Different-Input-Field-Relations` | FCMP.F | -- | Invalid (sNaN) |
| Special inputs | `Basic-Types-Inputs`, `Basic-Types-Intermediate`, `Input-Special-Significand` | all arith | RNE | Invalid, DivZero |
| Hamming distance | `Hamming-Distance` | all arith | RNE | Inexact |
| Fused multiply-add | `MultiplyAdd-*` | FMADD.F | all 4 | Invalid, Overflow, Underflow, Inexact |

**Excluded:** `Decimal-*` (sim8 does not support decimal FP).

### 8.14.5 Test Execution Methodology

The `.fptest` vector sets contain thousands of test cases. They are executed as **parametric tests** in the pysim8 pytest suite, not listed individually in this spec.

**Test runner pipeline:**

1. **Parse:** Read each `.fptest` file, skip header/comment lines, filter for `b32` prefix lines only (binary32 = float32).
2. **Decode operands:** Convert IBM FPgen hex-mantissa format (`+1.7FFFFDP-6`) to IEEE 754 binary32 bit pattern. Special tokens: `+Inf`, `-Inf`, `+Zero`, `-Zero`, `Q` (qNaN), `S` (sNaN).
3. **Configure FPCR:** Set rounding mode from the vector's rounding field. Clear FPSR via FCLR.
4. **Setup state:** Load operand1 into FA via FMOV.F. Store operand2 to a memory address.
5. **Execute:** Run the mapped sim8 instruction (FADD.F / FSUB.F / FMUL.F / FDIV.F / FCMP.F).
6. **Verify result:** Verify FA matches expected result **bitwise** (critical for NaN payload, Inf sign, signed zero). Verify FPSR flags match the exception flags from the vector.
7. **Reset:** Clear FPSR via FCLR, reset FPCR to defaults between vectors.

**Bitwise verification** is essential because IEEE 754 requires specific bit patterns for:
- NaN propagation (payload preserved, quiet bit set)
- Signed zero (+0.0 vs -0.0)
- Infinity sign
- Subnormal encoding

**Coverage categories and what they validate:**

| Category | `.fptest` file(s) | What it validates |
|----------|-------------------|-------------------|
| Cancellation | Add-Cancellation, Add-Cancellation-And-Subnorm-Result | Precision loss when subtracting nearly-equal values; guard/round/sticky bit correctness |
| Shift alignment | Add-Shift, Add-Shift-And-Special-Significands | Mantissa alignment for operands with large exponent difference; correct handling of shifted-out bits |
| Division | Divide-Trailing-Zeros, Divide-Divide-By-Zero-Exception | Division quotient precision; 0/0 and finite/0 exception behavior |
| Overflow | Overflow | Transition from max finite to Inf; correct rounding at the boundary; OF+NX flag interaction |
| Underflow | Underflow | Transition from normal to subnormal; gradual underflow; flush-to-zero boundary; UF+NX flag interaction |
| Rounding | Rounding, Corner-Rounding, Vicinity-Of-Rounding-Boundaries | All 4 IEEE 754 rounding modes; tie-breaking for RNE; boundary cases where rounding changes the exponent |
| Sticky bit | Sticky-Bit-Calculation | Correct computation of sticky bit during mantissa shift; sticky bit's effect on rounding decision |
| Compare | Compare-Different-Input-Field-Relations | All comparison orderings (less/equal/greater/unordered); sNaN Invalid exception on compare |
| Special values | Basic-Types-Inputs, Basic-Types-Intermediate, Input-Special-Significand | NaN, Inf, zero, subnorm as inputs to all operations; correct default results and exception flags |
| Hamming distance | Hamming-Distance | Operand pairs with specific bit difference patterns; exercises mantissa arithmetic edge cases |
| Fused multiply-add | MultiplyAdd-* | Fused multiply-accumulate precision; intermediate product not rounded before addition; Inf*0+x and sNaN exception behavior |

---

## 8.15 OFP8 (E4M3, E5M2) Tests

Tests that OFP8 8-bit formats work correctly. E4M3 has unique behavior: no Infinity, overflow saturates to ±448.

### 8.15.1 OFP8 Load/Store

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 152 | `FMOV.O3 FQA, [d]` | FQA = 1.0 (E4M3) | Load E4M3 from memory (1 byte) |
|     | `HLT` | | |
|     | `d: DB 1.0_o3` | | E4M3 1.0 |
| 153 | `FMOV.O2 FQA, [d]` | FQA = 1.0 (E5M2) | Load E5M2 from memory (1 byte) |
|     | `HLT` | | |
|     | `d: DB 1.0_o2` | | E5M2 1.0 |
| 154 | `FMOV.O3 FQA, [d]` | | FQA = 1.0 (E4M3) |
|     | `FMOV.O3 [0x60], FQA` | mem[0x60] = 0x38 | Store E4M3 to memory (1 byte) |
|     | `HLT` | | |
|     | `d: DB 1.0_o3` | | |

### 8.15.2 OFP8 Arithmetic

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 155 | `FMOV.O3 FQA, [d1]` | | FQA = 1.0 (E4M3) |
|     | `FADD.O3 FQA, [d2]` | FQA = 3.0 (E4M3) | E4M3 addition: 1.0 + 2.0 |
|     | `HLT` | | |
|     | `d1: DB 1.0_o3` | | |
|     | `d2: DB 2.0_o3` | | |

### 8.15.3 E4M3 Overflow Saturation

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 156 | `FMOV.O3 FQA, [d1]` | | FQA = 448.0 (max E4M3) |
|     | `FMUL.O3 FQA, [d2]` | FQA = 448.0 (E4M3), FPSR.OF=1 | 448 × 2 = overflow → saturates to ±448 (no Inf in E4M3) |
|     | `HLT` | state=HALTED | |
|     | `d1: DB 448.0_o3` | | max finite E4M3 |
|     | `d2: DB 2.0_o3` | | |

### 8.15.4 OFP8 Conversion and Classification

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 157 | `FMOV.F FA, [d]` | | FA = 1.5 (float32) |
|     | `FCVT.O3.F FQA, FA` | FQA = 1.5 (E4M3) | float32 → E4M3 (exact) |
|     | `HLT` | | |
|     | `d: DB 1.5` | | |
| 158 | `FMOV.O3 FQA, [d]` | | FQA = 1.0 (E4M3, positive normal) |
|     | `FCLASS.O3 A, FQA` | A=0x04 | NORM (bit 2) |
|     | `HLT` | | |
|     | `d: DB 1.0_o3` | | |

### 8.15.5 OFP8 Register-to-Register

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 159 | `FMOV.O3 FQA, [d1]` | | FQA = 1.0 (E4M3) |
|     | `FMOV.O3 FQB, [d2]` | | FQB = 2.0 (E4M3) |
|     | `FADD.O3 FQA, FQB` | FQA = 3.0 (E4M3) | E4M3 reg-reg addition |
|     | `HLT` | | |
|     | `d1: DB 1.0_o3` | | |
|     | `d2: DB 2.0_o3` | | |

### 8.15.6 OFP8 Encoding Verification

| # | Source | Expected bytes | Description |
|---|--------|--------------------|-------------|
| 160 | `FABS.O3 FQA` | `[142, 0x03]` | fmt=3, pos=0, phys=0 → FPM=0x03 |

---

## 8.16 FMOV Register-to-Register (Opcode 145)

Tests raw bit copy between FP registers.

### 8.16.1 Basic FMOV_RR

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 161 | `FMOV.H FHA, [d]` | | Load 1.5 float16 into FHA |
|     | `FMOV.H FHB, FHA` | FHB = 0x3E00 | Raw bit copy FHA → FHB |
|     | `HLT` | FPSR=0 | No exceptions |
|     | `d: DB 1.5_h` | | |
| 162 | `FMOV.F FA, [d]` | | Load 2.0 float32 |
|     | `FMOV.F FB, FA` | FB = 0x40000000 | Cross-physical raw bit copy |
|     | `HLT` | | |
|     | `d: DB 2.0` | | |
| 163 | `FMOV.O3 FQA, [d]` | | Load E4M3 1.0 |
|     | `FMOV.O3 FQB, FQA` | FQB = 0x38 | OFP8 reg-reg copy |
|     | `HLT` | | |
|     | `d: DB 1.0_o3` | | |

### 8.16.2 FMOV_RR Format Mismatch

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 164 | *(bytecode)* `[145, 0x01, 0x00]` | F=true, A=12 | dst=float16, src=float32 → FAULT(ERR_FP_FORMAT) |

### 8.16.3 FMOV_RR Cost

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 165 | `FMOV.H FHA, [d]` | cost(FMOV_RR)=1 | FMOV_RR costs 1 tick |
|     | `FMOV.H FHB, FHA` | | |
|     | `HLT` | | |
|     | `d: DB 1.5_h` | | |

### 8.16.4 FMOV_RR Encoding

| # | Source | Expected bytes | Description |
|---|--------|--------------------|-------------|
| 166 | `FMOV.H FHA, FHB` | `[145, 0x01, 0x09]` | Opcode 145, dst_fpm, src_fpm |

---

## 8.17 Test Summary

| Group | Tests | Coverage |
|-------|-------|----------|
| [FMOV](#82-fmov----fp-load--store) | 1-13 | FP load/store, all formats, DP, page boundary, aliasing, flags |
| [FP Arithmetic](#83-fp-arithmetic) | 14-22, 122-132 | FADD/FSUB/FMUL/FDIV memory + reg-reg, FMADD, float32/float16/bfloat16 |
| [FP Special Values](#84-fp-special-values) | 23-29 | Infinity, NaN, denormals, signed zero |
| [FP Compare](#85-fp-compare) | 30-37, 133-136 | FCMP/FCMP_RR flag mapping, Jcc integration, float16, NaN |
| [FP Unary + Classification](#86-fp-unary-operations) | 38-50, 137-144 | FABS, FNEG, FSQRT, FCLASS, Inf/NaN/float16, float16/bfloat16 |
| [FP Conversions](#87-fp-conversions) | 51-64 | FCVT, FITOF, FFTOI, saturation, edge cases |
| [FP Control](#88-fp-control-registers) | 65-73 | FPCR, FPSR, FCLR, GPR restriction |
| [FP Exception Model](#89-fp-exception-model) | 74-79 | All 5 exception types set flags, sticky accumulation |
| [FP Format Faults](#810-fp-format-faults) | 80-86 | Invalid FPM bytes, reserved 4-bit formats |
| [FP + Integer Flags](#811-fp--integer-flag-isolation) | 87-89 | Flag isolation between FP and integer ops |
| [FP Cost Model](#812-fp-cost-model-verification) | 90-96, 145-147 | Cycle costs for all FP categories incl. reg-reg, FCLASS, FMADD |
| [FP Assembler Encoding](#813-fp-assembler-encoding-verification) | 97-121, 148-151 | FPM encoding, instruction bytes, EXMY aliases, reg-reg/FCLASS/FMADD encoding, errors |
| [IEEE 754 Vectors](#814-ieee-754-arithmetic-validation) | (parametric) | Methodology + mapping spec for `.fptest` vector suites |
| [OFP8 (E4M3, E5M2)](#815-ofp8-e4m3-e5m2-tests) | 152-160 | OFP8 load/store, arithmetic, E4M3 overflow saturation, conversion, classification, reg-reg, encoding |
| [FMOV_RR](#816-fmov-register-to-register-opcode-145) | 161-166 | FMOV_RR basic, cross-phys, OFP8, format mismatch fault, cost, encoding |
| **Spec tests total** | **166** | **166 functional FP tests (sections 8.2-8.16)** |
| **Parametric (pysim8)** | **~1700+** | **Full `.fptest` b32 vector coverage via automated test runner** |
