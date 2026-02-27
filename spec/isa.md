# 1. Instruction Set Architecture (ISA)

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [Memory Model & Addressing](mem.md), [CPU Architecture](cpu.md), [Microarchitecture](uarch.md), [Assembler](asm.md), [Opcode Table](opcodes.md), [FPU](fp.md)

## 1.1 Overview

| Property | Value |
|----------|-------|
| Word Size | 8 bits |
| Address Space | 64 KB (256 pages × 256 bytes) |
| General Purpose Registers | 4 (A, B, C, D) |
| FP Registers | 1 physical × 32-bit (15 named sub-register views); see [FPU](fp.md) |
| Instruction Encoding | 1-4 bytes per instruction |

## 1.2 Registers

### General Purpose Registers

| Register | Code | Description |
|----------|------|-------------|
| A | 0 | Accumulator; implicit destination for MUL/DIV |
| B | 1 | General purpose |
| C | 2 | General purpose |
| D | 3 | General purpose |

### Special Purpose Registers

| Register | Code | Initial Value | Description |
|----------|------|---------------|-------------|
| IP | — | 0 | Instruction Pointer (internal, wider than 8 bits); not directly accessible |
| SP | 4 | 231 (0xE7) | Stack Pointer; grows downward |
| DP | 5 | 0 | Data Page register (0-255); selects active 256-byte page for data access |

**IP note:** IP is an 8-bit register (0–255). The fetch boundary check (`IP + len >= 256`) ensures IP never leaves this range; it triggers FAULT(5) before execution when an instruction would reach or cross the page 0 boundary. Jump/CALL/RET targets are 8-bit values and always stay in range.

**SP note:** SP (code 4) can be used as a register operand in MOV, ADD, SUB, INC, DEC, CMP instructions. It is **not** supported as operand in bitwise (AND/OR/XOR/NOT), shift (SHL/SHR), stack (PUSH/POP), jump, MUL, DIV, and CALL instructions.

**DP note:** DP (code 5) can be used in MOV instructions only. Any 8-bit value (0-255) is valid. DP affects all data addressing: both `[addr]` and `[reg±offset]`. Exceptions: `[SP±offset]` always uses page 0, as do jumps and CALL/RET.

**Clarification for PUSH [addr] / PUSH [reg]:** The source address uses DP (data is read from `DP × 256 + addr`), but the destination is always the stack in page 0. This is asymmetric by design — DP affects where data is *read from*, not where the stack resides.

### Status Flags

| Flag | Initial | Description |
|------|---------|-------------|
| Z | false | Zero flag — set when result equals 0 |
| C | false | Carry flag — see semantics below |
| F | false | Fault flag — set when CPU encounters an error |

**Carry flag semantics (verified by formal model):**

- **ADD/INC:** C=1 if result > 255 (unsigned overflow)
- **SUB/DEC/CMP:** C=1 if result < 0 (unsigned underflow, i.e., borrow)
- **MUL:** C=1 if result > 255
- **DIV:** C=0 always (quotient of two 8-bit values is always 0-255)
- **SHL:** C=1 if overflow (value × 2^n > 255)
- **SHR:** C=1 if any bits were shifted out (value mod 2^n ≠ 0)
- **AND/OR/XOR/NOT:** C=0 (always cleared)

**Arithmetic wraparound:** All arithmetic results are modulo 256 (range 0-255). The C flag indicates if wraparound occurred.

**Fault behavior:** When an error occurs, F is set to true and the error code is written to register A. The CPU enters FAULT state and stops execution. See [Error Codes](errors.md).

### Floating-Point Registers

The FPU provides one 32-bit physical register with 15 named sub-register views at 4 granularity levels:

| Register(s) | Width | Count | Description |
|-------------|-------|-------|-------------|
| FA | 32-bit | 1 | Full register |
| FHA, FHB | 16-bit | 2 | Half views (low, high) |
| FQA-FQD | 8-bit | 4 | Quarter views |
| FOA-FOH | 4-bit | 8 | Octet views |

**FP Control Registers:**

| Register | Width | Initial Value | Description |
|----------|-------|---------------|-------------|
| FPCR | 8-bit | 0 | FP Control: rounding mode |
| FPSR | 8-bit | 0 | FP Status: sticky exception flags |

For full register model, aliasing rules, and format details, see [FPU](fp.md).

## 1.3 Memory Model

For a concise reference on page layout, DP behavior, console I/O, and effective address formulas, see [Memory Model & Addressing](mem.md).

### Address Space Layout

Total: 64 KB organized as 256 pages of 256 bytes each.

**Initialization:** All memory is initialized to 0 at reset. Program code is loaded starting at address 0. The I/O region (232-255) displays as blank spaces initially.

| Page | Absolute Range | Usage |
|------|----------------|-------|
| 0 | 0x0000 - 0x00FF | Program, stack, page-0 data, I/O (0xE8-0xFF) |
| 1-255 | 0x0100 - 0xFFFF | Extended data (255 pages × 256 bytes = 65280 bytes) |

**Page 0 layout:**

| Region | Offset | Size | Usage |
|--------|--------|------|-------|
| Program/Data/Stack | 0x00 - 0xE7 | 232 bytes | Code, variables, stack |
| Console Output | 0xE8 - 0xFF | 24 bytes | Memory-mapped I/O |

**Key constraints:**

- IP always executes from page 0 (code should stay below address 232 to avoid overwriting the I/O region; the CPU enforces the page boundary at address 256, not 232). Executing code from the I/O region (232-255) is technically valid — no special protection exists.
- SP and stack operations always use page 0
- `[SP]` and `[SP±offset]` always access page 0 (stack-relative)
- JMP/CALL addresses are page-0 offsets (0-255)

**DP affects data access:**

- Direct addressing `[addr]` → effective address = `DP × 256 + addr`
- Register indirect `[A]`, `[B]`, `[C]`, `[D]` and `[reg±offset]` → effective address = `DP × 256 + reg + offset`
- At reset DP=0, so default behavior accesses page 0
- **I/O region (232-255) exists only on page 0.** There is no special handling — to access I/O, DP must be 0. When DP≠0, `[232]`-`[255]` access extended memory, not console.

See also: [DP interaction with I/O](mem.md#dp-interaction-important).

### Console Output (Memory-Mapped I/O)

Addresses 232-255 (0xE8-0xFF) on page 0 serve as a memory-mapped character display:

- Each byte is interpreted as an ASCII character code for display
- Writing to these addresses (via MOV or any store operation) updates the display
- Non-printable and whitespace characters render as blank space
- The region is readable and writable — no special access restrictions
- Display order: left to right, address 232 first, 255 last
- Total display capacity: 24 characters

## 1.4 Addressing Modes

For a single-page summary of effective address rules and the page-boundary fault, see [Effective Address Calculation](mem.md#effective-address-calculation).

| Mode | Syntax | Example | Effective Address |
|------|--------|---------|-------------------|
| Register | `reg` | `A`, `B`, `SP` | Direct register reference |
| Immediate | `const` | `42`, `0xFF` | Numeric constant (0-255) |
| Direct | `[addr]` or `[label]` | `[0x50]`, `[232]`, `[data]` | `DP × 256 + addr` |
| Register Indirect | `[reg±offset]` | `[B+4]`, `[C-2]` | `DP × 256 + reg + offset` |
| SP-Relative | `[SP±offset]` | `[SP-2]` | `SP + offset` (always page 0) |

**Register Indirect Encoding:** A single byte encodes both register and offset.

- Bits [2:0] — register code (0=A, 1=B, 2=C, 3=D, 4=SP); codes 5-7 cause FAULT (`ERR_INVALID_REG`, A=4; see [Error Codes](errors.md))
- Bits [7:3] — signed offset (-16 to +15), two's complement for negative values
- Encode: `encoded_byte = (offset_u << 3) | register_code`
  where `offset_u = offset` if ≥ 0, or `32 + offset` if < 0 (5-bit two's complement)
- Decode: `register = byte % 8`, `offset = byte >> 3`, if `offset > 15` then `offset -= 32`
- When offset is 0, behaves as simple register indirect `[reg]`
- **Effective address:**
  - For A, B, C, D: `DP × 256 + register_value + offset`
  - For SP: `register_value + offset` (always page 0)
- If `register_value + offset` is outside 0–255, the CPU enters **FAULT (A=5)** (page boundary violation; see [Error Codes](errors.md))
  - Error code: `ERR_PAGE_BOUNDARY` (A=5)

**Note:** `[addr]` (direct) and `[reg]` / `[reg±offset]` (register indirect) use different opcodes. The assembler distinguishes them by whether the content inside brackets is a number/label or a register name.

## 1.5 Instruction Reference

### HLT — Halt (Opcode 0)

| Mnemonic | Opcode | Bytes | Description |
|----------|--------|-------|-------------|
| HLT | 0 | 1 | Halt CPU execution |

**Note:** `HLT` is a valid assembler mnemonic. Alternatively, `DB 0` produces the same byte.

**IP behavior:** When `HLT` is encountered, the CPU enters the HALTED state and `IP` remains pointing at the `HLT` opcode byte.

### MOV — Data Movement (Opcodes 1-8)

| Operands | Opcode | Bytes | Description |
|----------|--------|-------|-------------|
| reg, reg | 1 | 3 | Copy register to register |
| reg, [addr] | 2 | 3 | Load from direct address |
| reg, [reg] | 3 | 3 | Load via register indirect |
| [addr], reg | 4 | 3 | Store to direct address |
| [reg], reg | 5 | 3 | Store via register indirect |
| reg, const | 6 | 3 | Load immediate |
| [addr], const | 7 | 3 | Store immediate to address |
| [reg], const | 8 | 3 | Store immediate via indirect |

### ADD — Addition (Opcodes 10-13)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 10 | 3 |
| reg, [reg] | 11 | 3 |
| reg, [addr] | 12 | 3 |
| reg, const | 13 | 3 |

### SUB — Subtraction (Opcodes 14-17)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 14 | 3 |
| reg, [reg] | 15 | 3 |
| reg, [addr] | 16 | 3 |
| reg, const | 17 | 3 |

### INC/DEC — Increment/Decrement (Opcodes 18-19)

| Mnemonic | Opcode | Bytes |
|----------|--------|-------|
| INC reg | 18 | 2 |
| DEC reg | 19 | 2 |

### CMP — Compare (Opcodes 20-23)

Sets flags without storing result.

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 20 | 3 |
| reg, [reg] | 21 | 3 |
| reg, [addr] | 22 | 3 |
| reg, const | 23 | 3 |

**Flags:** Z=1 if equal; C=1 if first < second (unsigned)

### JMP — Unconditional Jump (Opcodes 30-31)

| Operands | Opcode | Bytes | Description |
|----------|--------|-------|-------------|
| reg | 30 | 2 | Jump to address stored in register (indirect) |
| addr | 31 | 2 | Jump to immediate address |

### Conditional Jumps (Opcodes 32-43)

| Mnemonic | reg | addr | Condition |
|----------|-----|------|-----------|
| JC | 32 | 33 | C = 1 (carry) |
| JNC | 34 | 35 | C = 0 (no carry) |
| JZ | 36 | 37 | Z = 1 (zero) |
| JNZ | 38 | 39 | Z = 0 (not zero) |
| JA | 40 | 41 | C=0 AND Z=0 (above) |
| JNA | 42 | 43 | C=1 OR Z=1 (not above) |

**Aliases:** JB=JNAE=JC, JNB=JAE=JNC, JE=JZ, JNE=JNZ, JNBE=JA, JBE=JNA

**Important:** Jump and CALL register operands differ from other instructions:

- Syntax uses **plain register name** without brackets: `JMP A`, not `JMP [A]`
- Only GPR accepted (A, B, C, D) — SP is **not** supported
- Register indirect with offset is **not** supported for jumps
- The register's **value** is used as the target address (indirect semantics)

### Stack Operations (Opcodes 50-54)

| Mnemonic | Operands | Opcode | Bytes |
|----------|----------|--------|-------|
| PUSH | reg | 50 | 2 |
| PUSH | [reg] | 51 | 2 |
| PUSH | [addr] | 52 | 2 |
| PUSH | const | 53 | 2 |
| POP | reg | 54 | 2 |

**Stack mechanics:**

- PUSH: store value at memory[SP], then decrement SP (post-decrement)
- POP: increment SP (pre-increment), then load value from memory[SP]
- Stack grows downward from address 231 (0xE7) toward 0
- Stack overflow: attempting PUSH/CALL when SP = 0 → CPU enters **FAULT (A=2)** (see [Error Codes](errors.md))
- Stack underflow: attempting POP/RET when SP ≥ 231 → CPU enters **FAULT (A=3)** (see [Error Codes](errors.md))
- Bounds checking applies only to stack operations (PUSH, POP, CALL, RET). Arithmetic on SP via MOV, ADD, SUB, INC, DEC does **not** check bounds — the programmer is responsible for keeping SP within valid stack range.

**Note:** PUSH and POP direct register operands accept only GPR (A, B, C, D), not SP. However, SP may appear as a base in register indirect addressing: `PUSH [SP-2]` is valid.

### Subroutine Operations (Opcodes 55-57)

| Mnemonic | Operands | Opcode | Bytes |
|----------|----------|--------|-------|
| CALL | reg | 55 | 2 |
| CALL | addr | 56 | 2 |
| RET | — | 57 | 1 |

**CALL:** pushes return address (address of the next instruction after CALL) onto the stack, then jumps to the target address.

**RET:** pops address from the stack and jumps to it.

### MUL — Multiplication (Opcodes 60-63)

**Result:** A = A × operand

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg | 60 | 2 |
| [reg] | 61 | 2 |
| [addr] | 62 | 2 |
| const | 63 | 2 |

### DIV — Division (Opcodes 64-67)

**Result:** A = A ÷ operand (integer division)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg | 64 | 2 |
| [reg] | 65 | 2 |
| [addr] | 66 | 2 |
| const | 67 | 2 |

**Division by zero:** CPU enters **FAULT (A=1)** (see [Error Codes](errors.md)).

### AND — Bitwise AND (Opcodes 70-73)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 70 | 3 |
| reg, [reg] | 71 | 3 |
| reg, [addr] | 72 | 3 |
| reg, const | 73 | 3 |

### OR — Bitwise OR (Opcodes 74-77)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 74 | 3 |
| reg, [reg] | 75 | 3 |
| reg, [addr] | 76 | 3 |
| reg, const | 77 | 3 |

### XOR — Bitwise XOR (Opcodes 78-81)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 78 | 3 |
| reg, [reg] | 79 | 3 |
| reg, [addr] | 80 | 3 |
| reg, const | 81 | 3 |

### NOT — Bitwise Complement (Opcode 82)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg | 82 | 2 |

**Bitwise operations flags:** C flag is **cleared** (set to 0). Z flag is set if result equals 0. Only GPR (A, B, C, D) allowed as **destination** register operands; SP/DP as destination cause FAULT (`ERR_INVALID_REG`, A=4; see [Error Codes](errors.md)). Note: SP is valid as a base in `[SP±offset]` source addressing.

### SHL — Shift Left (Opcodes 90-93)

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 90 | 3 |
| reg, [reg] | 91 | 3 |
| reg, [addr] | 92 | 3 |
| reg, const | 93 | 3 |

**Alias:** `SAL` = `SHL`

### SHR — Shift Right (Opcodes 94-97)

Unsigned (logical) right shift (`>>>`).

| Operands | Opcode | Bytes |
|----------|--------|-------|
| reg, reg | 94 | 3 |
| reg, [reg] | 95 | 3 |
| reg, [addr] | 96 | 3 |
| reg, const | 97 | 3 |

**Alias:** `SAR` = `SHR` (both perform unsigned logical right shift; unlike x86, SAR does not preserve the sign bit)

**Shift operations:** Only GPR (A, B, C, D) allowed as **destination** operands; SP/DP as destination cause FAULT (`ERR_INVALID_REG`, A=4). SP is valid as a base in `[SP±offset]` source addressing. Shift amount can be 0-255; shifting by N≥8 bits produces 0.

- **SHL:** C = 1 if overflow (value × 2^n > 255)
- **SHR:** C = 1 if any bits were shifted out (value mod 2^n ≠ 0)
- **Shift by 0:** C is unchanged; Z is recomputed (based on the unchanged value)

### DB — Define Byte (Pseudo-instruction)

| Operands | Description |
|----------|-------------|
| const | Single byte |
| const, const, ... | Multiple bytes (comma-separated) |
| "string" | Multiple bytes (ASCII codes) |

## 1.6 Flag Behavior

Arithmetic operations set flags via the two-step carry+wrap logic below (see [pseudocode in uarch.md](uarch.md#42-flag-computation)). Shift and bitwise operations have explicit exceptions described in their instruction sections.

**Step 1 — Carry and wrapping:**

| Raw value | Carry | Wrapped result |
|-----------|-------|----------------|
| ≥ 256 | C = 1 | value % 256 |
| < 0 | C = 1 | (256 − (−value) % 256) % 256 |
| 0 .. 255 | C = 0 | value (unchanged) |

**Step 2 — Zero:** Z = 1 if the wrapped result equals 0, otherwise Z = 0.

C and Z can both be set simultaneously (e.g., `255 + 1` = 256 wraps to 0: C=1, Z=1).

**Applies to:** ADD, SUB, INC, DEC, CMP, MUL, DIV.

**Shift operations:** SHL and SHR compute carry and zero with their own rules (see [SHL](#shl--shift-left-opcodes-90-93) and [SHR](#shr--shift-right-opcodes-94-97)). Shift by 0 leaves C unchanged; Z is always recomputed.

**Bitwise operations:** AND, OR, XOR, NOT clear C flag (C=0) and set Z flag (based on result = 0).

**Flag-neutral instructions:** MOV, PUSH, POP, CALL, RET, JMP, and all conditional jumps do **not** affect flags. CMP sets flags without storing the result.

## 1.7 Assembly Syntax

```
[label:] mnemonic [operand1 [, operand2]]  [; comment]
```

**Number formats:** `200` (decimal), `200d` (decimal explicit), `0xC8` (hex), `0o310` (octal), `11001000b` (binary), `'A'` (char)

For label rules, comment syntax, and error handling, see [Assembler Specification](asm.md).

## 1.8 Instruction Encoding Format

All instructions are encoded as 1-4 bytes. Operand bytes follow syntactic operand order (see [FP encoding exceptions](#19-floating-point-instructions-opcodes-128-160) for FFTOI and FCLASS).

For the complete opcode mapping, see [Opcode Table](opcodes.md).

### Operand Byte Types

| Type | Size | Range | Description |
|------|------|-------|-------------|
| reg | 1 byte | 0-5 | Register code (0=A, 1=B, 2=C, 3=D, 4=SP, 5=DP) |
| reg_gpr | 1 byte | 0-3 | GPR-only register code (SP not allowed) |
| const | 1 byte | 0-255 | Immediate value |
| addr | 1 byte | 0-255 | Memory address |
| regaddr | 1 byte | 0-255 | Register indirect with offset (see [section 1.4](#14-addressing-modes)) |
| fpm | 1 byte | 0-255 | FP modifier byte: format + position + physical register (see [FPU](fp.md#75-fpm-byte-encoding)) |
| gpr | 1 byte | 0-3 | GPR-only code for FP↔integer conversion (A=0, B=1, C=2, D=3) |

### Encoding by Instruction Size

The tables below cover integer instructions (opcodes 0-97). For FP instruction encoding (opcodes 128-160, up to 4 bytes), see [FP Encoding Summary](#fp-encoding-summary).

**1-byte** `[opcode]`:

| Instructions |
|--------------|
| HLT (0), RET (57) |

**2-byte** `[opcode, operand]`:

| Category | Instructions | Operand byte |
|----------|-------------|--------------|
| INC/DEC | 18-19 | reg (0-4, SP allowed) |
| JMP/Jcc register | 30,32,34,36,38,40,42 | reg_gpr (0-3 only) |
| JMP/Jcc address | 31,33,35,37,39,41,43 | addr |
| PUSH reg | 50 | reg_gpr (0-3 only) |
| PUSH [reg] | 51 | regaddr |
| PUSH [addr] | 52 | addr |
| PUSH const | 53 | const |
| POP | 54 | reg_gpr (0-3 only) |
| CALL register | 55 | reg_gpr (0-3 only) |
| CALL address | 56 | addr |
| MUL/DIV reg | 60,64 | reg_gpr (0-3 only) |
| MUL/DIV [reg] | 61,65 | regaddr |
| MUL/DIV [addr] | 62,66 | addr |
| MUL/DIV const | 63,67 | const |
| NOT | 82 | reg_gpr (0-3 only) |

**3-byte** `[opcode, operand1, operand2]`:

| Category | Instructions | Operand 1 | Operand 2 |
|----------|-------------|-----------|-----------|
| MOV reg, reg | 1 | dest reg (0-5) | src reg (0-5) |
| MOV reg, [addr] | 2 | dest reg (0-5) | src addr |
| MOV reg, [reg] | 3 | dest reg (0-5) | src regaddr |
| MOV [addr], reg | 4 | dest addr | src reg (0-5) |
| MOV [reg], reg | 5 | dest regaddr | src reg (0-5) |
| MOV reg, const | 6 | dest reg (0-5) | src const |
| MOV [addr], const | 7 | dest addr | src const |
| MOV [reg], const | 8 | dest regaddr | src const |
| ADD/SUB/CMP | 10-17, 20-23 | dest reg (0-4) | src reg (0-4)/regaddr/addr/const |
| AND/OR/XOR | 70-81 | dest reg_gpr (0-3) | src reg_gpr/regaddr/addr/const |
| SHL/SHR | 90-97 | dest reg_gpr (0-3) | src reg_gpr/regaddr/addr/const |

### Encoding Examples

| Assembly | Bytes (decimal) | Explanation |
|----------|----------------|-------------|
| `HLT` | `0` | opcode only |
| `MOV A, B` | `1, 0, 1` | opcode=1, dest=A(0), src=B(1) |
| `MOV A, 42` | `6, 0, 42` | opcode=6, dest=A(0), value=42 |
| `MOV [232], A` | `4, 232, 0` | opcode=4, addr=232, src=A(0) |
| `MOV A, [B+2]` | `3, 0, 17` | opcode=3, dest=A(0), regaddr=(2\*8+1)=17 |
| `MOV A, [data]` | `2, 0, addr` | opcode=2, dest=A(0), addr from label resolution |
| `ADD A, 1` | `13, 0, 1` | opcode=13, dest=A(0), value=1 |
| `INC C` | `18, 2` | opcode=18, reg=C(2) |
| `CMP A, 0` | `23, 0, 0` | opcode=23, reg=A(0), value=0 |
| `JNZ label` | `39, addr` | opcode=39, addr from label resolution |
| `PUSH A` | `50, 0` | opcode=50, reg=A(0) |
| `CALL label` | `56, addr` | opcode=56, addr from label resolution |
| `RET` | `57` | opcode only |
| `DB "Hi"` | `72, 105` | raw bytes: 'H'=72, 'i'=105 |
| `DB 10, 20, 30` | `10, 20, 30` | comma-separated list of raw bytes |

## 1.9 Floating-Point Instructions (Opcodes 128-160)

The FPU adds 32 opcodes (128-160, except 145) for IEEE 754 floating-point operations. All FP data instructions use a format suffix in assembly and an FPM byte in encoding. For full instruction semantics, encoding details, and the FP exception model, see [FPU](fp.md).

### FP Instruction Summary

| Opcodes | Mnemonic | Category | Description |
|---------|----------|----------|-------------|
| 128-131 | FMOV | Data movement | Load/store between FP register and memory |
| 132-133 | FADD | Arithmetic | FP addition |
| 134-135 | FSUB | Arithmetic | FP subtraction |
| 136-137 | FMUL | Arithmetic | FP multiplication |
| 138-139 | FDIV | Arithmetic | FP division |
| 140-141 | FCMP | Compare | FP compare, sets integer Z/C flags |
| 142 | FABS | Unary | Absolute value (clear sign bit) |
| 143 | FNEG | Unary | Negate (toggle sign bit) |
| 144 | FSQRT | Unary | Square root |
| 145 | *(reserved)* | — | — |
| 146 | FCVT | Conversion | Convert between FP formats |
| 147 | FITOF | Conversion | uint8 (GPR) → FP |
| 148 | FFTOI | Conversion | FP → uint8 (GPR), saturating |
| 149 | FSTAT | Control | Read FPSR → GPR |
| 150 | FCFG | Control | Read FPCR → GPR |
| 151 | FSCFG | Control | Write GPR → FPCR |
| 152 | FCLR | Control | Clear all FPSR flags |
| 153 | FADD | Reg-reg arith | FP addition (register-to-register) |
| 154 | FSUB | Reg-reg arith | FP subtraction (register-to-register) |
| 155 | FMUL | Reg-reg arith | FP multiplication (register-to-register) |
| 156 | FDIV | Reg-reg arith | FP division (register-to-register) |
| 157 | FCMP | Reg-reg compare | FP compare (register-to-register), sets Z/C |
| 158 | FCLASS | Classification | Classify FP value → 8-bit mask in GPR |
| 159 | FMADD | Fused multiply-add | dst = src × mem[addr] + dst (direct) |
| 160 | FMADD | Fused multiply-add | dst = src × mem[reg] + dst (indirect) |

### FP Encoding Summary

| Size | Layout | Instructions |
|------|--------|-------------|
| 1 byte | `[opcode]` | FCLR |
| 2 bytes | `[opcode, fpm]` | FABS, FNEG, FSQRT |
| 2 bytes | `[opcode, gpr]` | FSTAT, FCFG, FSCFG |
| 3 bytes | `[opcode, fpm, addr/regaddr]` | FMOV, FADD, FSUB, FMUL, FDIV, FCMP (mem) |
| 3 bytes | `[opcode, dst_fpm, src_fpm]` | FCVT, FADD, FSUB, FMUL, FDIV, FCMP (reg-reg) |
| 3 bytes | `[opcode, fpm, gpr]` | FITOF, FFTOI, FCLASS |
| 4 bytes | `[opcode, dst_fpm, src_fpm, addr/regaddr]` | FMADD |

**Encoding order exception:** For FFTOI and FCLASS, the assembly operand order is `gpr, FP` (destination GPR first), but the encoding is `[opcode, fpm, gpr]` (FPM byte first). This is the only case where encoding byte order differs from assembly operand order — it keeps all FP↔integer conversion encodings uniform (`[opcode, fpm, gpr]` for FITOF, FFTOI, and FCLASS).

## 1.10 Error Codes

Error code definitions are in [Error Codes](errors.md).
