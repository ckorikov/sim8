# 4. Microarchitecture: Interpreter Model

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [CPU Architecture](cpu.md), [FPU](fp.md)

## 4.0 Pseudocode Conventions

The pseudocode in this section is language-agnostic. All values are integers unless specified.

- `DIV` is integer division: `a DIV b = floor(a / b)` for `b>0`.
- `mod` is mathematical modulo with a non-negative result: `x mod 256` is always in `0..255` (including for negative `x`).
- `2 ^ n` denotes exponentiation: $2^n$.
- `FAULT(code)` means: enter FAULT state by setting `state=FAULT`, set `F=true`, set `A=code`, and **immediately return** (non-local exit) — no further lines in the current handler or `step()` execute. Flags `Z` and `C` retain their pre-fault values. See [Error Codes](errors.md).
- `carry` and `zero` refer to the architectural flags `C` and `Z`.
- `memory[addr] = value` stores `value mod 256` (memory cells are 8-bit).

**Instruction stream:** Machine code is stored in memory. The opcode is fetched from `memory[IP]`, and operand bytes are fetched from `memory[IP + k]` as part of instruction decode.

Instruction length is opcode-dependent (1–4 bytes). Each instruction handler advances `IP` by its own encoded length (or assigns `IP` directly for control-flow instructions).

**Instruction fetch boundary:** If `IP + instrLength >= 256`, the instruction extends to or past the page 0 boundary. This is a `FAULT(5)` (`ERR_PAGE_BOUNDARY`) before any operand bytes are read. For example, a 3-byte instruction at IP=254 faults because 254 + 3 = 257 >= 256.

The CPU also maintains a control state variable:

- `state` ∈ {`IDLE`, `RUNNING`, `HALTED`, `FAULT`}
- `reset()` zeroes all memory (64 KB), initializes `state=IDLE`, and sets architectural registers/flags to their initial values as defined in [CPU Architecture](cpu.md#31-processor-states). `steps` and `cycles` are zeroed.

## 4.1 Execution Loop

Calling `step()` on a HALTED or FAULT CPU is a no-op (returns `false`, no state changes).

```
FUNCTION step():
    IF state == FAULT: RETURN false
    IF state == HALTED: RETURN false

    IF state == IDLE:
        state = RUNNING

    opcode = memory[IP]
    IF opcode == 0:
        // HLT encountered. IP remains pointing at the HLT opcode byte.
        state = HALTED
        RETURN false

    len = instructionLength(opcode)    // from opcode table; 0 if unassigned
    IF len == 0: FAULT(6)             // ERR_INVALID_OPCODE
    IF IP + len >= 256: FAULT(5)      // ERR_PAGE_BOUNDARY

    execute(opcode)
    IF state == FAULT: RETURN false
    steps = steps + 1
    cycles = cycles + cost(opcode)
    RETURN true                   // RUNNING
```

## 4.2 Flag Computation

**Carry semantics (formally verified):**

- For ADD: `carry = (result > 255)` — unsigned overflow
- For SUB/CMP: `carry = (result < 0)` — unsigned underflow (borrow)

```
FUNCTION checkOperation(value):
    // value can be negative (underflow) or > 255 (overflow)
    carry = (value < 0) OR (value > 255)
    value = value mod 256
    zero = (value == 0)
    RETURN value
```

## 4.3 Address Calculation

**Direct address** — always uses DP:

```
FUNCTION directAddress(addr_byte):
    RETURN DP * 256 + addr_byte
```

**Address bounds:** With `DP` and `addr_byte` as 8-bit values (0-255), `directAddress` always produces a valid absolute address in 0..65535.

**Note:** I/O region (232-255) exists only on page 0. To write to console, DP must be 0.

**Register indirect** — uses DP, except SP (always page 0):

```
FUNCTION indirectAddress(encoded_byte):
    reg = encoded_byte mod 8
    IF reg > 4: FAULT(4)  // ERR_INVALID_REG (only A,B,C,D,SP valid)

    offset = encoded_byte DIV 8
    IF offset > 15: offset = offset - 32

    IF reg == 4:
        base = SP
    ELSE:
        base = registers[reg]

    page_offset = base + offset
    IF page_offset < 0 OR page_offset > 255:
        FAULT(5)  // ERR_PAGE_BOUNDARY

    IF reg == 4:  // SP
        RETURN page_offset
    ELSE:
        RETURN DP * 256 + page_offset

FUNCTION instrByte(k):
    // Fetch the k-th byte of the current instruction (k=0 is opcode)
    // Caller guarantees IP + instrLength < 256 (checked at decode time)
    RETURN memory[IP + k]

FUNCTION decodeGPR(reg_code):
    // Accept A,B,C,D only
    IF reg_code > 3: FAULT(4)
    RETURN reg_code

FUNCTION decodeGPRorSP(reg_code):
    // Accept A,B,C,D,SP
    IF reg_code > 4: FAULT(4)
    RETURN reg_code

FUNCTION decodeMovReg(reg_code):
    // Accept A,B,C,D,SP,DP (DP is only valid for MOV forms)
    IF reg_code > 5: FAULT(4)
    RETURN reg_code
```

## 4.4 Instruction Handlers

**Note:** This section shows reference handlers for representative instruction forms to demonstrate the interpreter execution model. The complete instruction set (all opcode variants) is defined in [ISA](isa.md) and the opcode table in [Opcodes](opcodes.md). Any instruction form not listed here follows the same decode/validate conventions and uses the same effective-address and flag rules described above.

### Data Movement

**MOV reg, reg (Opcode 1):**

```
dest = decodeMovReg(instrByte(1))
src = decodeMovReg(instrByte(2))
IF src == 4:
    src_value = SP
ELSE IF src == 5:
    src_value = DP
ELSE:
    src_value = registers[src]

IF dest == 4:
    SP = src_value
ELSE IF dest == 5:
    DP = src_value
ELSE:
    registers[dest] = src_value
IP = IP + 3
```

**MOV reg, const (Opcode 6):**

```
dest = decodeMovReg(instrByte(1))
value = instrByte(2)
IF dest == 4: SP = value
ELSE IF dest == 5: DP = value
ELSE: registers[dest] = value
IP = IP + 3
```

**MOV reg, [addr] (Opcode 2):**

```
dest = decodeMovReg(instrByte(1))
addr = directAddress(instrByte(2))
value = memory[addr]
IF dest == 4: SP = value
ELSE IF dest == 5: DP = value
ELSE: registers[dest] = value
IP = IP + 3
```

**MOV reg, [reg] (Opcode 3):**

```
dest = decodeMovReg(instrByte(1))
addr = indirectAddress(instrByte(2))
value = memory[addr]
IF dest == 4: SP = value
ELSE IF dest == 5: DP = value
ELSE: registers[dest] = value
IP = IP + 3
```

**MOV [addr], reg (Opcode 4):**

```
addr = directAddress(instrByte(1))
src = decodeMovReg(instrByte(2))
IF src == 4:
    value = SP
ELSE IF src == 5:
    value = DP
ELSE:
    value = registers[src]
memory[addr] = value
IP = IP + 3
```

**MOV [reg], reg (Opcode 5):**

```
addr = indirectAddress(instrByte(1))
src = decodeMovReg(instrByte(2))
IF src == 4:
    value = SP
ELSE IF src == 5:
    value = DP
ELSE:
    value = registers[src]
memory[addr] = value
IP = IP + 3
```

### Arithmetic

**ADD reg, reg (Opcode 10):**

```
dest = decodeGPRorSP(instrByte(1))
src = decodeGPRorSP(instrByte(2))
IF dest == 4:
    left = SP
ELSE:
    left = registers[dest]

IF src == 4:
    right = SP
ELSE:
    right = registers[src]
result = checkOperation(left + right)
IF dest == 4: SP = result
ELSE: registers[dest] = result
IP = IP + 3
```

**ADD reg, [addr] (Opcode 12):**

```
dest = decodeGPRorSP(instrByte(1))
addr = directAddress(instrByte(2))
IF dest == 4:
    left = SP
ELSE:
    left = registers[dest]
result = checkOperation(left + memory[addr])
IF dest == 4: SP = result
ELSE: registers[dest] = result
IP = IP + 3
```

**SUB reg, const (Opcode 17):**

```
dest = decodeGPRorSP(instrByte(1))
value = instrByte(2)
IF dest == 4:
    left = SP
ELSE:
    left = registers[dest]
result = checkOperation(left - value)
IF dest == 4: SP = result
ELSE: registers[dest] = result
IP = IP + 3
```

**INC reg (Opcode 18):**

```
reg = decodeGPRorSP(instrByte(1))
IF reg == 4:
    value = SP
ELSE:
    value = registers[reg]
result = checkOperation(value + 1)
IF reg == 4: SP = result
ELSE: registers[reg] = result
IP = IP + 2
```

**CMP reg, const (Opcode 23):**

```
reg = decodeGPRorSP(instrByte(1))
value = instrByte(2)
IF reg == 4:
    left = SP
ELSE:
    left = registers[reg]
checkOperation(left - value)  // result discarded, only flags set
IP = IP + 3
```

### Jumps

**JMP reg (Opcode 30):**

```
reg = decodeGPR(instrByte(1))
IP = registers[reg]
```

**JMP addr (Opcode 31):**

```
target = instrByte(1)
IP = target
```

**JNZ addr (Opcode 39):**

```
target = instrByte(1)
IF NOT zero:
    IP = target
ELSE:
    IP = IP + 2
```

**JA addr (Opcode 41):**

```
target = instrByte(1)
IF (NOT carry) AND (NOT zero):
    IP = target
ELSE:
    IP = IP + 2
```

### Stack

**Note:** Validation occurs BEFORE any state modification (memory/SP changes).

**PUSH reg (Opcode 50):**

```
reg = decodeGPR(instrByte(1))
IF SP == 0: FAULT(2)      // ERR_STACK_OVERFLOW (check BEFORE write)
memory[SP] = registers[reg]
SP = SP - 1
IP = IP + 2
```

**PUSH [addr] (Opcode 52):**

```
addr = directAddress(instrByte(1))
IF SP == 0: FAULT(2)      // check BEFORE write
memory[SP] = memory[addr]
SP = SP - 1
IP = IP + 2
```

**PUSH const (Opcode 53):**

```
value = instrByte(1)
IF SP == 0: FAULT(2)      // check BEFORE write
memory[SP] = value
SP = SP - 1
IP = IP + 2
```

**POP reg (Opcode 54):**

```
reg = decodeGPR(instrByte(1))
IF SP >= 231: FAULT(3)    // ERR_STACK_UNDERFLOW (check BEFORE increment)
SP = SP + 1
registers[reg] = memory[SP]
IP = IP + 2
```

### Subroutines

**CALL reg (Opcode 55):**

```
reg = decodeGPR(instrByte(1))
IF SP == 0: FAULT(2)      // check BEFORE write
return_addr = IP + 2
memory[SP] = return_addr
SP = SP - 1
IP = registers[reg]
```

**CALL addr (Opcode 56):**

```
target = instrByte(1)
IF SP == 0: FAULT(2)      // check BEFORE write
return_addr = IP + 2
memory[SP] = return_addr
SP = SP - 1
IP = target
```

**Return address note:** If `IP + 2 > 255` (e.g., CALL at IP=254), the stored return address wraps modulo 256 per the memory write convention. In practice, executable code should stay below address 232 (I/O region).

**RET (Opcode 57):**

```
IF SP >= 231: FAULT(3)    // check BEFORE increment
SP = SP + 1
IP = memory[SP]
```

### Multiplication / Division

**MUL reg (Opcode 60):**

```
reg = decodeGPR(instrByte(1))
A = checkOperation(A * registers[reg])
IP = IP + 2
```

**MUL [addr] (Opcode 62):**

```
addr = directAddress(instrByte(1))
A = checkOperation(A * memory[addr])
IP = IP + 2
```

**DIV const (Opcode 67):**

```
value = instrByte(1)
IF value == 0: FAULT(1)  // ERR_DIV_ZERO
A = checkOperation(A DIV value)
IP = IP + 2
```

**DIV carry note:** `checkOperation` always sets C=0 for DIV because the quotient of two 8-bit values is always in 0–255.

### Bitwise

**Note:** Bitwise operations (AND, OR, XOR, NOT) clear C flag (C=0) and set Z flag based on the result.

**AND reg, const (Opcode 73):**

```
dest = decodeGPR(instrByte(1))
value = instrByte(2)
result = registers[dest] AND value
registers[dest] = result
carry = false
zero = (result == 0)
IP = IP + 3
```

**NOT reg (Opcode 82):**

```
reg = decodeGPR(instrByte(1))
result = registers[reg] XOR 255  // bitwise NOT (XOR 0xFF)
registers[reg] = result
carry = false
zero = (result == 0)
IP = IP + 2
```

**SHL reg, const (Opcode 93):**

```
dest = decodeGPR(instrByte(1))
count = instrByte(2)
value = registers[dest]
IF count == 0:
    result = value
    // C unchanged
ELSE:
    raw = value * (2 ^ count)
    carry = (raw > 255)          // overflow
    result = raw mod 256

registers[dest] = result
zero = (result == 0)
IP = IP + 3
```

**SHR reg, const (Opcode 97):**

```
dest = decodeGPR(instrByte(1))
count = instrByte(2)
value = registers[dest]
IF count == 0:
    result = value
    // C unchanged
ELSE:
    // any bits shifted out
    carry = ((value mod (2 ^ count)) != 0)
    result = value DIV (2 ^ count)

registers[dest] = result
zero = (result == 0)
IP = IP + 3
```

**Shift by N ≥ 8:** For SHL, `value * 2^N` is always > 255 for any nonzero `value`, so C=1 and result=0. For SHR, `value DIV 2^N` is always 0, and C=1 if `value` was nonzero. If `value` is 0, shifting by any amount gives result=0 with C=0.

For instruction encoding details, see [ISA section 1.8](isa.md#18-instruction-encoding-format).

## 4.5 Cost Model

The CPU maintains two monotonic counters:

- **steps** — number of executed instructions (excluding HLT and faults).
- **cycles** — simulation clock, sum of per-instruction costs in clock ticks.

Each instruction variant has an integer **cost** (in ticks). `reset()` zeroes both counters.

### Cost Assignment Rules

The CPU models three pipeline stages: **register** (1 tick), **memory** (2 ticks), and **expensive ALU** (2 ticks for MUL/DIV).

| Pipeline | Latency | Triggers |
|----------|---------|----------|
| Register / immediate / simple ALU | 1 | Register read/write, ADD/SUB/AND/OR/XOR/NOT/SHL/SHR, jumps |
| Memory | 2 | `[addr]`, `[reg]`, stack (PUSH/POP/CALL/RET) |
| Expensive ALU (MUL/DIV) | 2 | Multiplication, division |

**Scheduling rule:** Independent pipelines execute in parallel — cost = **max**. When one pipeline's output feeds another pipeline's input (data dependency), they execute sequentially — cost = **sum**.

**Pipeline stages and their latencies:**

| Stage | Latency | Notes |
|-------|---------|-------|
| Register read / writeback | 0 | Free — part of any pipeline's final stage |
| Simple ALU (ADD, SUB, AND, OR, XOR, NOT, SHL, SHR, CMP) | 1 | |
| Memory access (read or write) | 2 | `[addr]`, `[reg]`, stack |
| Expensive ALU (MUL, DIV) | 2 | |

**Scheduling rule:** Independent stages execute in parallel — cost = **max**. When one stage's output feeds another stage's input (data dependency), they execute sequentially — cost = **sum**.

**Resulting costs per category:**

| Category | Cost | Rule | Examples |
|----------|------|------|---------|
| Register-only / register-immediate | 1 | alu(1) | `MOV A, B`, `ADD A, 5`, `INC A`, `NOT A` |
| Conditional / unconditional jumps | 1 | alu(1) | `JMP addr`, `JZ addr`, `JA reg` |
| Memory read or write (no ALU) | 2 | mem(2) | `MOV A, [addr]` = 2, `MOV [B], 5` = 2 |
| Stack operations | 2 | mem(2) | `PUSH A` = 2, `POP A` = 2, `CALL` = 2, `RET` = 2 |
| MUL / DIV (register or immediate) | 2 | alu(2) | `MUL B` = 2, `DIV 3` = 2 |
| Simple ALU + memory | **3** | mem(2) + alu(1), dependency | `ADD A, [addr]` = 3, `CMP A, [B]` = 3 |
| Stack + memory operand | **4** | mem(2) + mem(2), dependency | `PUSH [addr]` = 4, `PUSH [B]` = 4 |
| MUL / DIV + memory | **4** | mem(2) + alu(2), dependency | `MUL [addr]` = 4, `DIV [B]` = 4 |
| HLT | 0 | Not counted in steps or cycles | `HLT` |

### Fault Semantics

If an instruction raises a FAULT, neither `steps` nor `cycles` is incremented.

### Configuration

Cost defaults are derived from the rules above and encoded per instruction variant in the implementation. A simulator may accept per-mnemonic overrides at construction time:

```
cpu = CPU(costs={"MUL": 8})   // all MUL variants become cost 8
```

An override replaces the cost for **all** variants of the given mnemonic.

## 4.6 FPU Pipeline

The FPU adds a new pipeline stage and extends the cost model.

### FPU Pipeline Stage

| Stage | Latency | Notes |
|-------|---------|-------|
| FPU (classify) | 2 | FCLASS — bit inspection, no arithmetic |
| FPU (basic) | 3 | FABS, FNEG, FCVT, FITOF, FFTOI |
| FPU (FSQRT) | 4 | Square root is more expensive |
| FPU (FMADD) | 4 | Fused multiply-add (FPU portion) |

### FP Cost Assignment

| Category | Cost | Rule | Examples |
|----------|------|------|---------|
| FP unary (no mem) | 3 | fpu(3) | FABS, FNEG |
| FCLASS | 2 | fpu(2) | Classification only, no memory access |
| FP reg-reg arith | 3 | fpu(3) | FADD, FSUB, FMUL, FDIV, FCMP (reg-reg) |
| FSQRT | 4 | fpu(4) | FSQRT |
| FP move (load/store) | 2 | mem(2) | FMOV |
| FP binary + mem | 5 | mem(2) + fpu(3), dependency | FADD, FSUB, FMUL, FDIV, FCMP (mem) |
| FMADD | 6 | mem(2) + fpu(4), dependency | Fused multiply-add |
| FP conversion | 3 | fpu(3) | FCVT, FITOF, FFTOI |
| FP control | 1 | reg(1) | FSTAT, FCFG, FSCFG, FCLR |

**Scheduling:** FP binary operations with memory (FADD, FSUB, FMUL, FDIV, FCMP, opcodes 132-141) read memory first (2 ticks), then perform the FP computation (3 ticks). These are sequential (data dependency) so cost = 2 + 3 = 5. Reg-reg variants (153-157) skip the memory stage: cost = 3. FMADD reads memory (2 ticks) then performs the fused multiply-add (4 ticks): cost = 2 + 4 = 6.

## 4.7 FPU Pseudocode

### FPM Decode

```
FUNCTION decodeFPM(fpm_byte):
    fmt  = fpm_byte mod 8
    pos  = (fpm_byte DIV 8) mod 8
    phys = fpm_byte DIV 64

    // v2 validation
    IF phys != 0: FAULT(12)       // ERR_FP_FORMAT: only register 0
    IF fmt == 7: FAULT(12)        // ERR_FP_FORMAT: reserved code
    IF fmt >= 5: FAULT(12)        // ERR_FP_FORMAT: reserved 4-bit formats (sub-byte)

    // Position validation
    IF fmt == 0 AND pos != 0: FAULT(12)   // .F: only pos 0
    IF fmt == 1 AND pos > 1: FAULT(12)    // .H: pos 0-1
    IF fmt == 2 AND pos > 1: FAULT(12)    // .BF: pos 0-1
    IF fmt == 3 AND pos > 3: FAULT(12)    // .O3: pos 0-3
    IF fmt == 4 AND pos > 3: FAULT(12)    // .O2: pos 0-3

    RETURN (fmt, pos, phys)
```

### FP Format Width

```
FUNCTION fpWidth(fmt):
    IF fmt == 0: RETURN 32     // .F
    IF fmt == 1: RETURN 16     // .H
    IF fmt == 2: RETURN 16     // .BF
    IF fmt == 3: RETURN 8      // .O3
    IF fmt == 4: RETURN 8      // .O2
    IF fmt == 5: RETURN 4      // .N1
    IF fmt == 6: RETURN 4      // .N2
```

### FP Sub-Register Access

```
FUNCTION fpRead(fmt, pos):
    // Read bits from the 32-bit physical register FA
    width = fpWidth(fmt)
    bit_offset = pos * width
    mask = (2 ^ width) - 1
    RETURN (FA DIV (2 ^ bit_offset)) mod (2 ^ width)

FUNCTION fpWrite(fmt, pos, value):
    // Write bits to the 32-bit physical register FA
    width = fpWidth(fmt)
    bit_offset = pos * width
    mask = (2 ^ width) - 1
    // Clear target bits, then set new value
    FA = (FA AND NOT (mask * (2 ^ bit_offset))) OR ((value mod (2 ^ width)) * (2 ^ bit_offset))
```

### FP Memory Read/Write

```
FUNCTION fpMemRead(addr, width):
    // Read width/8 bytes from memory, little-endian
    byte_count = width DIV 8
    page_offset = addr mod 256
    IF page_offset + byte_count - 1 > 255: FAULT(5)  // ERR_PAGE_BOUNDARY

    value = 0
    FOR i = 0 TO byte_count - 1:
        value = value + memory[addr + i] * (2 ^ (i * 8))
    RETURN value

FUNCTION fpMemWrite(addr, width, value):
    // Write width/8 bytes to memory, little-endian
    byte_count = width DIV 8
    page_offset = addr mod 256
    IF page_offset + byte_count - 1 > 255: FAULT(5)  // ERR_PAGE_BOUNDARY

    FOR i = 0 TO byte_count - 1:
        memory[addr + i] = (value DIV (2 ^ (i * 8))) mod 256
```

### FP Exception Handling

FP arithmetic operations collect a set of raised exceptions, then set the corresponding FPSR sticky flags:

```
FUNCTION fpRaiseExceptions(raised_set):
    // raised_set: bitmask of exceptions that occurred
    //   bit 0=Invalid, 1=DivZero, 2=Overflow, 3=Underflow, 4=Inexact
    // Set all applicable sticky flags (OR into FPSR)
    FPSR = FPSR OR raised_set
```

FP arithmetic exceptions never cause FAULT. The operation produces the IEEE 754 default result and execution continues. Programs detect exceptions by reading FPSR via `FSTAT`. See [FPU Exception Model](fp.md#77-fp-exception-model).

### Representative Instruction Handlers

**FMOV FP, [addr] (Opcode 128):**

```
(fmt, pos, phys) = decodeFPM(instrByte(1))
addr = directAddress(instrByte(2))
width = fpWidth(fmt)
value = fpMemRead(addr, width)
fpWrite(fmt, pos, value)
IP = IP + 3
```

**FADD FP, [addr] (Opcode 132):**

```
(fmt, pos, phys) = decodeFPM(instrByte(1))
addr = directAddress(instrByte(2))
width = fpWidth(fmt)
mem_value = fpMemRead(addr, width)
reg_value = fpRead(fmt, pos)
// Interpret both as FP in the format specified by fmt, add
result = fp_add(reg_value, mem_value, fmt)  // IEEE 754 add
// fp_add sets FPSR sticky flags via fpRaiseExceptions
fpWrite(fmt, pos, result)
IP = IP + 3
```

**FCMP FP, [addr] (Opcode 140):**

```
(fmt, pos, phys) = decodeFPM(instrByte(1))
addr = directAddress(instrByte(2))
width = fpWidth(fmt)
mem_value = fpMemRead(addr, width)
reg_value = fpRead(fmt, pos)
// Compare and set integer flags
IF isNaN(reg_value, fmt) OR isNaN(mem_value, fmt):
    zero = true; carry = true        // Unordered
    // If sNaN: fpRaiseExceptions(1)  // Invalid flag
ELSE IF fp_equal(reg_value, mem_value, fmt):
    zero = true; carry = false       // Equal
ELSE IF fp_less(reg_value, mem_value, fmt):
    zero = false; carry = true       // Less than
ELSE:
    zero = false; carry = false      // Greater than
IP = IP + 3
```

**FFTOI gpr, FP (Opcode 148):**

```
(fmt, pos, phys) = decodeFPM(instrByte(1))
gpr = instrByte(2)
IF gpr > 3: FAULT(4)                // ERR_INVALID_REG
fp_value = fpRead(fmt, pos)
// Convert FP to integer with saturation
int_value = fp_to_uint8(fp_value, fmt, FPCR)  // uses rounding mode
// fp_to_uint8 sets FPSR flags: Invalid (NaN/Inf) or Inexact
registers[gpr] = int_value
IP = IP + 3
```
