# 7. Floating-Point Unit (FPU)

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model](mem.md), [CPU Architecture](cpu.md), [Microarchitecture](uarch.md), [Opcodes](opcodes.md), [Error Codes](errors.md), [Assembler](asm.md)

## 7.1 Overview

The FPU is a coprocessor extension that adds IEEE 754 floating-point support to the sim8 integer CPU.

| Property | Value |
|----------|-------|
| Physical FP registers | 2 (FA, FB) |
| Register width | 32 bits |
| Named sub-register views | 30 (FA-FB, FHA-FHD, FQA-FQH, FOA-FOP) |
| Active formats (v2) | float32 (E8M23), float16 (E5M10), bfloat16 (E8M7), OFP8 (E4M3, E5M2) |
| Reserved formats | 4-bit (E2M1, E1M2) — sub-byte, incompatible with byte-addressable memory |
| Control registers | FPCR (rounding mode), FPSR (sticky exception flags) |
| FP opcodes | 33 (opcodes 128-162 except 163+) |
| FP fault codes | 1 (ERR_FP_FORMAT, code 12) |
| Memory byte order | Little-endian |

## 7.2 FP Register Model

### Physical Registers

Two 32-bit physical FP registers (phys=0: FA, phys=1: FB), each with named views at multiple granularity levels. Naming convention: **F + width prefix + position letter**.

```
FA (phys=0)                                    FB (phys=1)
bits[31:0]                                     bits[31:0]
┌───────────────────┬───────────────────┐      ┌───────────────────┬───────────────────┐
│       FHB         │       FHA         │      │       FHD         │       FHC         │
│     [31:16]       │     [15:0]        │      │     [31:16]       │     [15:0]        │
├─────────┬─────────┼─────────┬─────────┤      ├─────────┬─────────┼─────────┬─────────┤
│   FQD   │   FQC   │   FQB   │   FQA   │      │   FQH   │   FQG   │   FQF   │   FQE   │
│ [31:24] │ [23:16] │  [15:8] │  [7:0]  │      │ [31:24] │ [23:16] │  [15:8] │  [7:0]  │
├────┬────┼────┬────┼────┬────┼────┬────┤      ├────┬────┼────┬────┼────┬────┼────┬────┤
│FOH │FOG │FOF │FOE │FOD │FOC │FOB │FOA │      │FOP │FOO │FON │FOM │FOL │FOK │FOJ │FOI │
└────┴────┴────┴────┴────┴────┴────┴────┘      └────┴────┴────┴────┴────┴────┴────┴────┘
```

### Sub-Register Table

**Physical register 0 (FA):**

| Name | Bits     | Width | Position | Phys | Naming         |
|------|----------|-------|----------|------|----------------|
| FA   | [31:0]   | 32    | 0        | 0    | Full           |
| FHA  | [15:0]   | 16    | 0        | 0    | Half A         |
| FHB  | [31:16]  | 16    | 1        | 0    | Half B         |
| FQA  | [7:0]    | 8     | 0        | 0    | Quarter A      |
| FQB  | [15:8]   | 8     | 1        | 0    | Quarter B      |
| FQC  | [23:16]  | 8     | 2        | 0    | Quarter C      |
| FQD  | [31:24]  | 8     | 3        | 0    | Quarter D      |
| FOA  | [3:0]    | 4     | 0        | 0    | Octet A        |
| FOB  | [7:4]    | 4     | 1        | 0    | Octet B        |
| FOC  | [11:8]   | 4     | 2        | 0    | Octet C        |
| FOD  | [15:12]  | 4     | 3        | 0    | Octet D        |
| FOE  | [19:16]  | 4     | 4        | 0    | Octet E        |
| FOF  | [23:20]  | 4     | 5        | 0    | Octet F        |
| FOG  | [27:24]  | 4     | 6        | 0    | Octet G        |
| FOH  | [31:28]  | 4     | 7        | 0    | Octet H        |

**Physical register 1 (FB):**

| Name | Bits     | Width | Position | Phys | Naming         |
|------|----------|-------|----------|------|----------------|
| FB   | [31:0]   | 32    | 0        | 1    | Full           |
| FHC  | [15:0]   | 16    | 0        | 1    | Half C         |
| FHD  | [31:16]  | 16    | 1        | 1    | Half D         |
| FQE  | [7:0]    | 8     | 0        | 1    | Quarter E      |
| FQF  | [15:8]   | 8     | 1        | 1    | Quarter F      |
| FQG  | [23:16]  | 8     | 2        | 1    | Quarter G      |
| FQH  | [31:24]  | 8     | 3        | 1    | Quarter H      |
| FOI  | [3:0]    | 4     | 0        | 1    | Octet I        |
| FOJ  | [7:4]    | 4     | 1        | 1    | Octet J        |
| FOK  | [11:8]   | 4     | 2        | 1    | Octet K        |
| FOL  | [15:12]  | 4     | 3        | 1    | Octet L        |
| FOM  | [19:16]  | 4     | 4        | 1    | Octet M        |
| FON  | [23:20]  | 4     | 5        | 1    | Octet N        |
| FOO  | [27:24]  | 4     | 6        | 1    | Octet O        |
| FOP  | [31:28]  | 4     | 7        | 1    | Octet P        |

### Aliasing Rules

Writing to a wider view overwrites all narrower views it contains. Each physical register is independent — writing to FA does not affect FB, and vice versa.

**Physical register 0 (FA):**

- Writing to **FA** overwrites FHA, FHB, FQA-FQD, FOA-FOH.
- Writing to **FHA** overwrites FQA, FQB, FOA-FOD.
- Writing to **FHB** overwrites FQC, FQD, FOE-FOH.
- Writing to **FQA** overwrites FOA, FOB.
- Writing to **FQB** overwrites FOC, FOD.
- Writing to **FQC** overwrites FOE, FOF.
- Writing to **FQD** overwrites FOG, FOH.
- Writing to an **FO\*** register overwrites only those 4 bits.

**Physical register 1 (FB):** Same aliasing pattern with corresponding names (FB ↔ FHC/FHD ↔ FQE-FQH ↔ FOI-FOP).

No automatic format conversion occurs on aliased reads. Reading FHA after writing FA returns the raw low 16 bits, not a float16 conversion of the float32 value.

### v2 Scope and Future Expansion

**v2 scope:** Two physical registers (FA, FB) and their named sub-register views are fully operational. FA/FB, FHA-FHD are fully operational (float32, float16, bfloat16). FQA-FQH are fully operational (OFP8 E4M3, E5M2). FOA-FOP are defined in encoding but FP operations on 4-bit formats are permanently reserved — executing them triggers FAULT(`ERR_FP_FORMAT`). The 4-bit formats (E2M1, E1M2) are sub-byte and fundamentally incompatible with the byte-addressable memory model (the smallest memory unit is 8 bits). FOA-FOP sub-register views remain accessible through aliasing (writing to a wider view that contains them).

**FPM encoding:** The FPM byte uses 2 bits for physical register selection (phys 0-3). Only phys 0 (FA) and phys 1 (FB) are valid in v2; phys 2-3 are reserved for future expansion.

## 7.3 FP Formats

### EXMY Notation

Every FP format is described using **EXMY notation**: E = exponent bits, M = mantissa bits, total width = E + M + 1 (sign bit).

### Predefined Formats

| EXMY   | Name     | Bits | Sign | Exp | Mantissa | Bias | Short suffix | Registers   | v2 status |
|--------|----------|------|------|-----|----------|------|--------------|-------------|-----------|
| E8M23  | float32  | 32   | 1    | 8   | 23       | 127  | `.F`         | FA, FB      | Active    |
| E5M10  | float16  | 16   | 1    | 5   | 10       | 15   | `.H`         | FHA-FHD     | Active    |
| E8M7   | bfloat16 | 16   | 1    | 8   | 7        | 127  | `.BF`        | FHA-FHD     | Active    |
| E4M3   | OFP8     | 8    | 1    | 4   | 3        | 7    | `.O3`        | FQA-FQH     | Active    |
| E5M2   | OFP8     | 8    | 1    | 5   | 2        | 15   | `.O2`        | FQA-FQH     | Active    |
| E2M1   | (4-bit)  | 4    | 1    | 2   | 1        | 1    | `.N1`        | FOA-FOP         | Reserved  |
| E1M2   | (4-bit)  | 4    | 1    | 1   | 2        | 1    | `.N2`        | FOA-FOP         | Reserved  |

### Special Values

Active formats follow IEEE 754 conventions for special values:

| Pattern | Value |
|---------|-------|
| Exponent = all 1s, mantissa = 0 | ±Infinity (sign bit determines sign) |
| Exponent = all 1s, mantissa ≠ 0 | NaN (quiet if MSB of mantissa = 1, signaling otherwise) |
| Exponent = 0, mantissa = 0 | ±0.0 (sign bit determines sign) |
| Exponent = 0, mantissa ≠ 0 | Denormalized (subnormal) number |

**OFP8 E4M3 exception:** E4M3 has **no Infinity representation** (per OCP MX specification). Only the single bit pattern with exponent = all 1s (1111) AND mantissa = all 1s (111) is NaN. All other max-exponent patterns are finite numbers. Max finite value = ±448. Overflow in E4M3 saturates to ±448 (not ±Inf).

**OFP8 E5M2:** Follows standard IEEE 754 conventions — exponent all 1s + mantissa 0 = ±Inf, mantissa ≠ 0 = NaN. Max finite value = ±57344.

### NaN Propagation

When an operation has one or more NaN inputs:

1. If any input is a signaling NaN (sNaN), set the Invalid flag.
2. Return a quiet NaN (qNaN). If one input is a qNaN, propagate it. If both are NaN, propagate the FP register operand's NaN (the register is always the "first" operand; memory is the "second").
3. The quiet NaN is formed by setting the MSB of the mantissa to 1 (quieting the sNaN).

### Signed Zero

`+0.0` and `-0.0` compare as equal.

## 7.4 Control Registers

### FPCR — FP Control Register (8-bit)

Controls rounding mode.

| Bits  | Field | Description        | Reset |
|-------|-------|--------------------|-------|
| [1:0] | RM    | Rounding mode      | 00    |
| [7:2] | —     | Reserved           | 0     |

Writes via `FSCFG` mask bits [7:2] to zero; only RM is writable.

**Rounding modes:**

| RM | Mode | Description |
|----|------|-------------|
| 00 | RNE  | Round to Nearest, ties to Even (IEEE 754 default) |
| 01 | RTZ  | Round toward Zero |
| 10 | RDN  | Round toward −∞ (floor) |
| 11 | RUP  | Round toward +∞ (ceiling) |

### FPSR — FP Status Register (8-bit)

Contains sticky IEEE 754 exception flags. Flags are **sticky**: once set, they remain set until explicitly cleared via `FCLR`.

| Bits  | Field | Description           | Reset |
|-------|-------|-----------------------|-------|
| [0]   | NV    | Invalid (sticky)      | 0     |
| [1]   | DZ    | Division by zero      | 0     |
| [2]   | OF    | Overflow              | 0     |
| [3]   | UF    | Underflow             | 0     |
| [4]   | NX    | Inexact               | 0     |
| [7:5] | —     | Reserved              | 0     |

## 7.5 FPM Byte Encoding

All FP instructions that touch FP data use a 1-byte **FP Modifier (FPM)** to encode the target sub-register and format.

### Bit Layout

```
  7   6   5   4   3   2   1   0
┌───┬───┬───┬───┬───┬───┬───┬───┐
│ phys  │    pos    │    fmt    │
└───┴───┴───┴───┴───┴───┴───┴───┘
```

| Bits   | Field | Description |
|--------|-------|-------------|
| [2:0]  | fmt   | Format code (0-7) |
| [5:3]  | pos   | Position within width class (0-7) |
| [7:6]  | phys  | Physical register selector (0-3; v2: 0-1 only) |

### Format Codes

| fmt | Suffix  | EXMY   | Width | Valid pos values |
|-----|---------|--------|-------|------------------|
| 0   | .F      | E8M23  | 32    | 0 only (→ FA)    |
| 1   | .H      | E5M10  | 16    | 0-1 (→ FHA, FHB) |
| 2   | .BF     | E8M7   | 16    | 0-1 (→ FHA, FHB) |
| 3   | .O3     | E4M3   | 8     | 0-3 (→ FQA-FQD)  |
| 4   | .O2     | E5M2   | 8     | 0-3 (→ FQA-FQD)  |
| 5   | .N1     | E2M1   | 4     | 0-7 (→ FOA-FOH)  |
| 6   | .N2     | E1M2   | 4     | 0-7 (→ FOA-FOH)  |
| 7   | —       | —      | —     | reserved          |

### Validation

The CPU validates the FPM byte on decode. Any of the following conditions triggers FAULT(`ERR_FP_FORMAT`):

- `phys > 1` (v2: only physical registers 0 and 1 exist)
- `fmt == 7` (reserved format code)
- `fmt ≥ 5` (reserved 4-bit formats in v2 — sub-byte, not memory-addressable)
- `pos` out of range for the given `fmt` (e.g., `pos > 0` for fmt=0, `pos > 3` for fmt=3/4)

### Common FPM Values (phys=0)

| Assembly         | fmt | pos | FPM byte   | Hex  |
|------------------|-----|-----|------------|------|
| `.F` FA          | 0   | 0   | 00 000 000 | 0x00 |
| `.H` FHA         | 1   | 0   | 00 000 001 | 0x01 |
| `.H` FHB         | 1   | 1   | 00 001 001 | 0x09 |
| `.BF` FHA        | 2   | 0   | 00 000 010 | 0x02 |
| `.BF` FHB        | 2   | 1   | 00 001 010 | 0x0A |
| `.O3` FQA        | 3   | 0   | 00 000 011 | 0x03 |
| `.O3` FQB        | 3   | 1   | 00 001 011 | 0x0B |
| `.O3` FQC        | 3   | 2   | 00 010 011 | 0x13 |
| `.O3` FQD        | 3   | 3   | 00 011 011 | 0x1B |
| `.O2` FQA        | 4   | 0   | 00 000 100 | 0x04 |
| `.O2` FQB        | 4   | 1   | 00 001 100 | 0x0C |
| `.O2` FQC        | 4   | 2   | 00 010 100 | 0x14 |
| `.O2` FQD        | 4   | 3   | 00 011 100 | 0x1C |

### FPM Byte Encoding Formula

```
FPM = (phys << 6) | (pos << 3) | fmt
```

Decode:
```
fmt  = FPM & 0x07
pos  = (FPM >> 3) & 0x07
phys = (FPM >> 6) & 0x03
```

## 7.6 Instruction Reference

All FP instructions use opcodes 128-162. For the master opcode table, see [Opcodes](opcodes.md).

### Instruction Encoding

FP instructions follow the general sim8 encoding model (1-4 bytes):

| Size | Layout | Instructions |
|------|--------|-------------|
| 1 byte | `[opcode]` | FCLR (152) |
| 2 bytes | `[opcode, fpm]` | FABS (142), FNEG (143), FSQRT (144) |
| 2 bytes | `[opcode, gpr]` | FSTAT (149), FCFG (150), FSCFG (151) |
| 3 bytes | `[opcode, fpm, addr/reg/fpm2/gpr/imm8]` | FMOV (128-131, 145, 161), FADD (132-133), FSUB (134-135), FMUL (136-137), FDIV (138-139), FCMP (140-141), FCVT (146), FITOF (147), FFTOI (148), FADD_RR-FCMP_RR (153-157), FCLASS (158) |
| 4 bytes | `[opcode, fpm, imm16_lo, imm16_hi]` | FMOV (162) |
| 4 bytes | `[opcode, dst_fpm, src_fpm, addr/regaddr]` | FMADD (159-160) |

**Note on 2-byte control instructions:** FSTAT (149), FCFG (150), and FSCFG (151) use the second byte as a GPR code (0-3), not an FPM byte.

**Common exceptions (apply to all FP instructions unless stated otherwise):**
- **ERR_FP_FORMAT (12):** All instructions with an FPM byte can raise this if the FPM is invalid.
- **ERR_PAGE_BOUNDARY (5):** All instructions with a memory operand can raise this if the multi-byte access crosses a page boundary.
- **ERR_INVALID_REG (4):** All instructions with a `regaddr` or `gpr` operand can raise this for invalid register codes.

Per-instruction exception lists below document only **IEEE 754 arithmetic exceptions** specific to that operation.

### FMOV — FP Move / Load / Store (Opcodes 128-131)

| Opcode | Operands      | Bytes | Encoding                | Description |
|--------|---------------|-------|-------------------------|-------------|
| 128    | FP, [addr]    | 3     | `[128, fpm, addr]`      | Load from direct address |
| 129    | FP, [reg]     | 3     | `[129, fpm, regaddr]`   | Load via register indirect |
| 130    | [addr], FP    | 3     | `[130, fpm, addr]`      | Store to direct address |
| 131    | [reg], FP     | 3     | `[131, fpm, regaddr]`   | Store via register indirect |

**Semantics:**
- Load: Read `width/8` bytes from memory starting at effective address (little-endian), store into the sub-register identified by FPM.
- Store: Read the sub-register value, write `width/8` bytes to memory starting at effective address (little-endian).
- Effective address: `DP × 256 + addr` (same as integer MOV). See [Memory Model](mem.md).
- Page boundary: if `page_offset + (width/8) - 1 > 255` → FAULT(`ERR_PAGE_BOUNDARY`).

**Flags:** No flags affected (like integer MOV).

**IEEE 754 exceptions:** None (FMOV is a data transfer, not an arithmetic operation).

### FMOV — FP Immediate Load (Opcodes 161-162)

| Opcode | Operands    | Bytes | Encoding                          | Description |
|--------|-------------|-------|-----------------------------------|-------------|
| 161    | FP, imm8    | 3     | `[161, fpm, imm8]`               | Load 8-bit FP immediate (OFP8) |
| 162    | FP, imm16   | 4     | `[162, fpm, imm16_lo, imm16_hi]` | Load 16-bit FP immediate (float16/bfloat16) |

**Semantics:** Write the raw FP bits from the immediate operand to the sub-register identified by FPM. This is a raw bit write (like FMOV load from memory), not an arithmetic operation. The assembler encodes the float literal into the instruction bytes at assembly time; the CPU stores the raw bits verbatim.

**Format validation (decode-time):**
- Opcode 161: fmt must be 3 or 4 (8-bit formats: OFP8 E4M3, E5M2). If fmt is not 3 or 4 → FAULT(`ERR_FP_FORMAT`).
- Opcode 162: fmt must be 1 or 2 (16-bit formats: float16, bfloat16). If fmt is not 1 or 2 → FAULT(`ERR_FP_FORMAT`).
- Standard FPM validation also applies (phys ≤ 1, pos in range for fmt).

**Float32 restriction:** float32 immediate is not supported because it would require 6 bytes (opcode + FPM + 4 immediate bytes), exceeding the 4-byte maximum instruction length. Use FMOV from memory instead.

**Byte order:** imm16 is little-endian (low byte first), consistent with FMOV memory byte order.

**Flags:** No flags affected.

**IEEE 754 exceptions:** None (raw bit transfer).

**Cost:** 1 tick.

### FADD — FP Addition (Opcodes 132-133)

| Opcode | Operands      | Bytes | Encoding                | Description |
|--------|---------------|-------|-------------------------|-------------|
| 132    | FP, [addr]    | 3     | `[132, fpm, addr]`      | FP += mem |
| 133    | FP, [reg]     | 3     | `[133, fpm, regaddr]`   | FP += mem (indirect) |

**Semantics:** Read `width/8` bytes from memory, interpret as the format specified by FPM, add to the FP sub-register value, store result back into the sub-register.

**Flags:** No integer flags affected.

**IEEE 754 exceptions:** Invalid (Inf + (-Inf), sNaN input), Overflow, Underflow, Inexact.

### FSUB — FP Subtraction (Opcodes 134-135)

| Opcode | Operands      | Bytes | Encoding                | Description |
|--------|---------------|-------|-------------------------|-------------|
| 134    | FP, [addr]    | 3     | `[134, fpm, addr]`      | FP -= mem |
| 135    | FP, [reg]     | 3     | `[135, fpm, regaddr]`   | FP -= mem (indirect) |

**Semantics:** Read value from memory, subtract from FP sub-register, store result.

**IEEE 754 exceptions:** Invalid (Inf - Inf with same sign, sNaN), Overflow, Underflow, Inexact.

### FMUL — FP Multiplication (Opcodes 136-137)

| Opcode | Operands      | Bytes | Encoding                | Description |
|--------|---------------|-------|-------------------------|-------------|
| 136    | FP, [addr]    | 3     | `[136, fpm, addr]`      | FP *= mem |
| 137    | FP, [reg]     | 3     | `[137, fpm, regaddr]`   | FP *= mem (indirect) |

**Semantics:** Read value from memory, multiply with FP sub-register, store result.

**IEEE 754 exceptions:** Invalid (0 × Inf, sNaN), Overflow, Underflow, Inexact.

### FDIV — FP Division (Opcodes 138-139)

| Opcode | Operands      | Bytes | Encoding                | Description |
|--------|---------------|-------|-------------------------|-------------|
| 138    | FP, [addr]    | 3     | `[138, fpm, addr]`      | FP /= mem |
| 139    | FP, [reg]     | 3     | `[139, fpm, regaddr]`   | FP /= mem (indirect) |

**Semantics:** Read value from memory, divide FP sub-register by it, store result.

**IEEE 754 exceptions:** Invalid (0/0, Inf/Inf, sNaN), DivZero (finite / ±0.0), Overflow, Underflow, Inexact.

### FCMP — FP Compare (Opcodes 140-141)

| Opcode | Operands      | Bytes | Encoding                | Description |
|--------|---------------|-------|-------------------------|-------------|
| 140    | FP, [addr]    | 3     | `[140, fpm, addr]`      | Compare, set Z/C |
| 141    | FP, [reg]     | 3     | `[141, fpm, regaddr]`   | Compare (indirect), set Z/C |

**Semantics:** Read value from memory, compare with FP sub-register, set integer Z and C flags.

**Flag mapping (reuses integer Z/C flags):**

| Condition       | Z | C | Integer jump |
|-----------------|---|---|--------------|
| FP == mem       | 1 | 0 | JZ           |
| FP < mem        | 0 | 1 | JC / JB      |
| FP > mem        | 0 | 0 | JA           |
| Unordered (NaN) | 1 | 1 | (unique)     |

**Note:** +0.0 and -0.0 compare as equal (Z=1, C=0).

**IEEE 754 exceptions:** Invalid (comparison with sNaN). Comparison with qNaN sets Unordered without raising Invalid.

### FABS — FP Absolute Value (Opcode 142)

| Opcode | Operands | Bytes | Encoding        | Description |
|--------|----------|-------|-----------------|-------------|
| 142    | FP       | 2     | `[142, fpm]`    | Clear sign bit |

**Semantics:** Clear the sign bit of the FP sub-register value (result is always non-negative).

**Flags:** No flags affected.

**IEEE 754 exceptions:** None (FABS is a bit manipulation).

### FNEG — FP Negate (Opcode 143)

| Opcode | Operands | Bytes | Encoding        | Description |
|--------|----------|-------|-----------------|-------------|
| 143    | FP       | 2     | `[143, fpm]`    | Flip sign bit |

**Semantics:** Toggle the sign bit of the FP sub-register value.

**Flags:** No flags affected.

**IEEE 754 exceptions:** None (FNEG is a bit manipulation).

### FSQRT — FP Square Root (Opcode 144)

| Opcode | Operands | Bytes | Encoding        | Description |
|--------|----------|-------|-----------------|-------------|
| 144    | FP       | 2     | `[144, fpm]`    | Square root |

**Semantics:** Compute the square root of the FP sub-register value, store result back.

**Flags:** No flags affected.

**IEEE 754 exceptions:** Invalid (sqrt of negative number, sNaN), Inexact. sqrt(±0) = ±0, sqrt(+Inf) = +Inf.

### FMOV — FP Register-to-Register Copy (Opcode 145)

| Opcode | Operands       | Bytes | Encoding                    | Description |
|--------|----------------|-------|-----------------------------|-------------|
| 145    | dst_FP, src_FP | 3     | `[145, dst_fpm, src_fpm]`   | Raw bit copy src → dst |

**Semantics:** Read the raw bits from the source FP sub-register, write them verbatim to the destination FP sub-register. No rounding, no IEEE 754 exceptions, no format conversion — this is a pure bit copy.

**Format constraint:** The format (fmt field) of dst_fpm and src_fpm must be identical. If `dst_fmt != src_fmt`, the CPU raises FAULT(`ERR_FP_FORMAT`). The position (pos field) and physical register (phys field) may differ — for example, `FMOV.H FHA, FHB` is valid (both fmt=1, but different positions).

**Assembly syntax:** `FMOV.fmt dst_reg, src_reg` (single suffix, two FP register operands, no brackets). Example: `FMOV.H FHA, FHB`.

**Flags:** No flags affected.

**IEEE 754 exceptions:** None (raw bit transfer).

**Cost:** 1 tick.

### FCVT — FP Format Conversion (Opcode 146)

| Opcode | Operands       | Bytes | Encoding              | Description |
|--------|----------------|-------|-----------------------|-------------|
| 146    | dst_FP, src_FP | 3     | `[146, dst_fpm, src_fpm]` | Convert between formats |

**Semantics:** Read the value from the source FP sub-register (interpreted in source format), convert to the destination format, store in the destination FP sub-register.

**Assembly syntax:** `FCVT.dst_fmt.src_fmt dst_reg, src_reg` (dual suffix). Example: `FCVT.H.F FHA, FA` converts float32 in FA to float16 in FHA.

**Same-format restriction (assembler):** The assembler rejects `FCVT` when the destination and source formats are identical (e.g., `FCVT.H.H FHA, FHB`). Use `FMOV` for same-format register copies instead. This is an assembler-level restriction only — the CPU does not fault on same-format FCVT in bytecode.

**Flags:** No flags affected.

**IEEE 754 exceptions:** Invalid (sNaN), Overflow (value too large for destination format), Underflow, Inexact.

### FITOF — Integer to FP Conversion (Opcode 147)

| Opcode | Operands   | Bytes | Encoding           | Description |
|--------|------------|-------|--------------------|-------------|
| 147    | FP, gpr    | 3     | `[147, fpm, gpr]`  | uint8 → FP |

**Semantics:** Read the 8-bit unsigned integer value from the GPR (A, B, C, D), convert to the FP format specified by FPM, store in the FP sub-register.

**Flags:** No flags affected.

**IEEE 754 exceptions:** Inexact (if the integer value cannot be exactly represented in the target format — possible only for formats with very small mantissa, e.g., bfloat16 for large uint8 values).

**Note:** The GPR operand byte is a register code (0-3). Codes 4-5 (SP, DP) are invalid → FAULT(`ERR_INVALID_REG`).

### FFTOI — FP to Integer Conversion (Opcode 148)

| Opcode | Operands   | Bytes | Encoding           | Description |
|--------|------------|-------|--------------------|-------------|
| 148    | gpr, FP    | 3     | `[148, fpm, gpr]`  | FP → uint8 (saturating) |

**Semantics:** Read the FP sub-register value, convert to an unsigned 8-bit integer using the current rounding mode (FPCR.RM), store in the GPR.

**Conversion rule:** The FP value is first rounded to an integer using the current rounding mode (FPCR.RM), then clamped to the uint8 range.

**Saturation rules (applied after rounding):**
- Rounded value > 255: result = 255
- Rounded value < 0: result = 0
- NaN: result = 0, Invalid exception raised
- +Inf: result = 255, Invalid exception raised
- -Inf: result = 0, Invalid exception raised

**Rounding examples:** With value 254.7: RNE → 255, RTZ → 254, RDN → 254, RUP → 255. With value 255.3: RNE → 255 (exact), RTZ → 255, RDN → 255, RUP → 256 → saturates to 255.

**Flags:** No integer flags affected. (The GPR value changes, but Z/C are not updated.)

**IEEE 754 exceptions:** Invalid (NaN, ±Inf), Inexact (fractional part discarded).

### FSTAT — Read FP Status (Opcode 149)

| Opcode | Operands | Bytes | Encoding         | Description |
|--------|----------|-------|------------------|-------------|
| 149    | gpr      | 2     | `[149, gpr]`     | FPSR → GPR |

**Semantics:** Copy the FPSR value into the specified GPR.

**Flags:** No flags affected.

**Note:** The second byte is a GPR code (0-3), not an FPM byte.

### FCFG — Read FP Configuration (Opcode 150)

| Opcode | Operands | Bytes | Encoding         | Description |
|--------|----------|-------|------------------|-------------|
| 150    | gpr      | 2     | `[150, gpr]`     | FPCR → GPR |

**Semantics:** Copy the FPCR value into the specified GPR.

**Flags:** No flags affected.

### FSCFG — Write FP Configuration (Opcode 151)

| Opcode | Operands | Bytes | Encoding         | Description |
|--------|----------|-------|------------------|-------------|
| 151    | gpr      | 2     | `[151, gpr]`     | GPR → FPCR |

**Semantics:** Write the GPR value into FPCR. Reserved bits [7:2] are masked to 0 on write; only RM [1:0] is writable.

**Flags:** No flags affected.

### FCLR — Clear FP Status Flags (Opcode 152)

| Opcode | Operands | Bytes | Encoding    | Description |
|--------|----------|-------|-------------|-------------|
| 152    | —        | 1     | `[152]`     | Clear all FPSR flags |

**Semantics:** Set FPSR to 0 (clear all sticky exception flags).

**Flags:** No integer flags affected.

### Register-to-Register Arithmetic (Opcodes 153-157)

| Opcode | Mnemonic | Operands        | Bytes | Encoding                   | Description |
|--------|----------|-----------------|-------|----------------------------|-------------|
| 153    | FADD_RR  | dst_FP, src_FP  | 3     | `[153, dst_fpm, src_fpm]`  | dst += src |
| 154    | FSUB_RR  | dst_FP, src_FP  | 3     | `[154, dst_fpm, src_fpm]`  | dst -= src |
| 155    | FMUL_RR  | dst_FP, src_FP  | 3     | `[155, dst_fpm, src_fpm]`  | dst *= src |
| 156    | FDIV_RR  | dst_FP, src_FP  | 3     | `[156, dst_fpm, src_fpm]`  | dst /= src |
| 157    | FCMP_RR  | dst_FP, src_FP  | 3     | `[157, dst_fpm, src_fpm]`  | Compare dst with src, set Z/C |

**Semantics:** Perform the arithmetic operation between two FP sub-registers (dst and src). The result is stored in the dst sub-register (except FCMP_RR, which only sets flags).

**Format constraint:** The format (fmt field) of dst_fpm and src_fpm must be identical. If `dst_fmt != src_fmt`, the CPU raises FAULT(`ERR_FP_FORMAT`). The position (pos field) may differ -- for example, `FADD_RR.H FHA, FHB` is valid (both fmt=1, but pos 0 and 1 respectively).

**FCMP_RR flag mapping:** Same as memory-variant FCMP (see above). Sets integer Z and C flags.

**Flags:** FADD_RR, FSUB_RR, FMUL_RR, FDIV_RR: no integer flags affected. FCMP_RR: sets Z and C.

**IEEE 754 exceptions:** Same as the corresponding memory-variant operations:
- **FADD_RR:** Invalid (Inf + (-Inf), sNaN), Overflow, Underflow, Inexact.
- **FSUB_RR:** Invalid (Inf - Inf same sign, sNaN), Overflow, Underflow, Inexact.
- **FMUL_RR:** Invalid (0 * Inf, sNaN), Overflow, Underflow, Inexact.
- **FDIV_RR:** Invalid (0/0, Inf/Inf, sNaN), DivZero (finite / +/-0.0), Overflow, Underflow, Inexact.
- **FCMP_RR:** Invalid (sNaN). Comparison with qNaN sets Unordered without raising Invalid.

**NaN propagation:** When both operands are NaN, propagate the dst operand's NaN (dst is always the "first" operand).

**Cost:** 3 ticks.

### FCLASS — FP Classify (Opcode 158)

| Opcode | Operands | Bytes | Encoding           | Description |
|--------|----------|-------|--------------------|-------------|
| 158    | gpr, FP  | 3     | `[158, fpm, gpr]`  | Classify FP value, write bitmask to GPR |

**Semantics:** Examine the FP sub-register value identified by FPM and produce an 8-bit classification bitmask. The bitmask is written to the specified GPR (A, B, C, D).

**Bitmask layout:**

| Bit | Flag | Condition |
|-----|------|-----------|
| 0   | ZERO | Value is +/-0.0 |
| 1   | SUB  | Value is subnormal (denormalized) |
| 2   | NORM | Value is a normal number |
| 3   | INF  | Value is +/-Infinity |
| 4   | NAN  | Value is a quiet NaN |
| 5   | SNAN | Value is a signaling NaN |
| 6   | NEG  | Sign bit is set (negative) |
| 7   | —    | Reserved (always 0) |

Exactly one of bits 0-5 is set per classification. Bit 6 (NEG) is set independently when the sign bit is 1, and can combine with any of bits 0-5 (e.g., -0.0 produces ZERO | NEG = 0x41, -Inf produces INF | NEG = 0x48).

**Flags:** No integer flags (Z, C) affected. FPSR is not modified.

**Faults:**
- **ERR_FP_FORMAT (12):** Invalid FPM byte.
- **ERR_INVALID_REG (4):** GPR code > 3.

**IEEE 754 exceptions:** None.

**Cost:** 2 ticks.

### FMADD — FP Fused Multiply-Accumulate (Opcodes 159-160)

| Opcode | Operands               | Bytes | Encoding                         | Description |
|--------|------------------------|-------|----------------------------------|-------------|
| 159    | dst_FP, src_FP, [addr] | 4     | `[159, dst_fpm, src_fpm, addr]`     | dst = src * mem[addr] + dst |
| 160    | dst_FP, src_FP, [reg]  | 4     | `[160, dst_fpm, src_fpm, regaddr]`  | dst = src * mem[regaddr] + dst |

**Note:** FMADD is the first 4-byte instruction in the sim8 ISA.

**Semantics:** Read `width/8` bytes from memory at the effective address (using the dst format's width), interpret as the same FP format, multiply with the src sub-register value, add the dst sub-register value, and store the result in the dst sub-register. The operation is: `dst = src * mem[addr] + dst`.

**Format constraint:** The format (fmt field) of dst_fpm and src_fpm must be identical. If `dst_fmt != src_fmt`, the CPU raises FAULT(`ERR_FP_FORMAT`). The position (pos field) may differ.

**Memory operand:** The memory value is interpreted using the same format as dst/src. Effective address calculation and page boundary checks follow the standard rules (see [Memory Model](mem.md)).

**Flags:** No integer flags affected.

**IEEE 754 exceptions:**
- **NV (Invalid):** Inf * 0, sNaN input.
- **OF (Overflow):** Result magnitude exceeds format range.
- **UF (Underflow):** Result is subnormal or underflows to zero.
- **NX (Inexact):** Result requires rounding.

**Faults:**
- **ERR_FP_FORMAT (12):** Invalid FPM byte, or dst_fmt != src_fmt.
- **ERR_PAGE_BOUNDARY (5):** Multi-byte memory access crosses page boundary.
- **ERR_INVALID_REG (4):** Invalid register code for indirect variant (opcode 160).

**Cost:** 6 ticks.

## 7.7 FP Exception Model

### Exception Flags

Each IEEE 754 exception type has a corresponding **sticky flag** in FPSR:

| Exception | FPSR flag | Default result |
|-----------|-----------|----------------|
| Invalid   | NV (bit 0) | qNaN          |
| DivZero   | DZ (bit 1) | ±Inf          |
| Overflow  | OF (bit 2) | ±Inf (RNE/RDN/RUP) or ±max finite (RTZ); **E4M3: always ±448** (no Inf) |
| Underflow | UF (bit 3) | Denormalized result or ±0.0 |
| Inexact   | NX (bit 4) | Correctly rounded result |

### Processing Rule

When an FP arithmetic operation raises an IEEE 754 exception:

1. Set the corresponding FPSR sticky flag(s).
2. Produce the IEEE 754 default result.
3. Continue execution.

FP arithmetic exceptions never cause FAULT. Programs detect exceptions by reading FPSR via `FSTAT` after computation.

### ERR_FP_FORMAT

**ERR_FP_FORMAT (code 12)** is a decode-time error, not an arithmetic exception. It always causes FAULT when the FPM byte is invalid (see § 7.5 Validation). It is unrelated to IEEE 754 exception flags.

## 7.8 Assembly Syntax

For complete FP assembly syntax rules — mandatory format suffixes, EXMY aliases, suffix-register width validation, FCVT dual suffix, control instruction syntax, FP register names, and case-insensitivity rules — see [Assembler Specification](asm.md#56-fp-assembly-syntax).

**Quick reference:**

```asm
FADD.F     FA, [addr]       ; float32 (suffix mandatory)
FADD.E8M23 FA, [addr]       ; same (EXMY alias)
FADD.H     FHA, [addr]      ; float16
FADD.BF    FHA, [addr]      ; bfloat16
FADD.O3    FQA, [addr]      ; OFP8 E4M3
FADD.O2    FQA, [addr]      ; OFP8 E5M2
FCVT.H.F   FHA, FA          ; format conversion (dual suffix)
FSTAT A                      ; control (no suffix)
FCLR                         ; clear flags (no suffix)
```

## 7.9 References

| Standard | Description | Used for |
|----------|-------------|----------|
| IEEE 754-2019 | IEEE Standard for Floating-Point Arithmetic | float32 (binary32), float16 (binary16), rounding modes, exception flags, NaN/Inf/denormal semantics |
| bfloat16 | Brain Floating Point (Google Brain) | E8M7 format: 8-bit exponent, 7-bit mantissa, same range as float32 |
| OFP8 (E4M3, E5M2) | Open Compute Project 8-bit FP | Active in v2. E4M3: no Infinity, max ±448, overflow saturates. E5M2: standard IEEE 754 (Inf, NaN) |
