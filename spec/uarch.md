# 3. Microarchitecture: Interpreter Model

> Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [CPU Architecture](cpu.md)

## 3.0 Pseudocode Conventions

The pseudocode in this section is language-agnostic. All values are integers unless specified.

- `DIV` is integer division: `a DIV b = floor(a / b)` for `b>0`.
- `mod` is mathematical modulo with a non-negative result: `x mod 256` is always in `0..255` (including for negative `x`).
- `2 ^ n` denotes exponentiation: $2^n$.
- `FAULT(code)` means: enter FAULT state by setting `state=FAULT`, set `F=true`, set `A=code`, and stop executing the current instruction/step (see [Error Codes](errors.md)).
- `carry` and `zero` refer to the architectural flags `C` and `Z`.

**Instruction stream:** Machine code is stored in memory. The opcode is fetched from `memory[IP]`, and operand bytes are fetched from `memory[IP + k]` as part of instruction decode.

Instruction length is opcode-dependent (1–3 bytes). Each instruction handler advances `IP` by its own encoded length (or assigns `IP` directly for control-flow instructions).

The CPU also maintains a control state variable:

- `state` ∈ {`IDLE`, `RUNNING`, `HALTED`, `FAULT`}
- `reset()` initializes `state=IDLE` and architectural registers/flags as defined in [CPU Architecture](cpu.md#21-processor-states).

## 3.1 Execution Loop

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

    execute(opcode)
    IF state == FAULT: RETURN false
    RETURN true                   // RUNNING
```

## 3.2 Flag Computation

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

## 3.3 Address Calculation

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

## 3.4 Instruction Handlers

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

**CALL addr (Opcode 56):**
```
target = instrByte(1)
IF SP == 0: FAULT(2)      // check BEFORE write
return_addr = IP + 2
memory[SP] = return_addr
SP = SP - 1
IP = target
```

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

### Bitwise

**Note:** Bitwise operations (AND, OR, XOR, NOT) set only Z flag; C flag is unchanged (ARM-style).

**AND reg, const (Opcode 73):**
```
dest = decodeGPR(instrByte(1))
value = instrByte(2)
result = registers[dest] AND value
registers[dest] = result
zero = (result == 0)       // C unchanged
IP = IP + 3
```

**NOT reg (Opcode 82):**
```
reg = decodeGPR(instrByte(1))
result = registers[reg] XOR 255  // bitwise NOT (XOR 0xFF)
registers[reg] = result
zero = (result == 0)            // C unchanged
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

For instruction encoding details, see [ISA section 1.8](isa.md#18-instruction-encoding-format).
