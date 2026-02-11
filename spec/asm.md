# 4. Assembler Specification

> Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [Instruction Encoding](isa.md#18-instruction-encoding-format)

## 4.1 Two-Pass Assembly

**Pass 1 — Code Generation:**

For each source line:

1. Parse an optional label, mnemonic, and operands.
1. If a label is present, record its address as the current output position.
1. If a mnemonic is present, determine the opcode from the mnemonic + operand types and emit opcode + operand bytes.
1. Record a source mapping (output position → source line) for diagnostics.
1. If the line is neither a label, instruction, blank, nor comment → syntax error.

Forward label references may be left unresolved during pass 1.

**Pass 2 — Label Resolution:**

Resolve all label references in operands to their numeric addresses. If a label is not found, report an "Undefined label" error.

## 4.2 Assembler Output

The assembler produces:

- Machine code as a sequence of bytes (each 0–255)
- A label table (label name → address)
- A source mapping (output position → source line number) for diagnostics

**Note:** DB pseudo-instructions are not CPU instructions and may be excluded from source-to-instruction mapping.

## 4.3 Labels

- Defined with trailing colon: `start:`, `.loop:`
- Must start with a letter or dot, followed by word characters: `/^[.A-Za-z]\w*$/`
- Case-insensitive duplicate detection (`Start` and `start` are the same label)
- Forbidden names: `A`, `B`, `C`, `D`, `SP`, `DP` (conflict with register names)
- Forward references allowed — a label can be used before its definition
- Dot-prefix labels supported for local scope convention: `.loop`, `.end`

## 4.4 Comments

- Semicolon (`;`) begins a comment
- Standalone comment lines: `; this is a comment`
- Inline comments after instructions: `MOV A, 5 ; load value`
- Empty lines are allowed

## 4.5 Register Operands

| Register | Code | Allowed as operand |
|----------|------|-------------------|
| A, B, C, D | 0-3 | All instructions that accept registers |
| SP | 4 | MOV, ADD, SUB, INC, DEC, CMP; also as base in `[SP±offset]` |
| DP | 5 | MOV only (`MOV DP, x` or `MOV x, DP`) |

**DP (Data Page):** Controls which 256-byte page is accessed by all data addressing: both `[addr]` (direct) and `[reg±offset]` (indirect). It does not affect control flow (jumps/CALL/RET) or the fact that PUSH/POP always write to the stack on page 0. **Console I/O is memory-mapped on page 0**, so to access `[232]..[255]` as I/O via direct addressing, software must use `DP=0`. See [Memory Model & Addressing](mem.md).

**SP in indirect addressing:** `[SP±offset]` always uses page 0, regardless of DP. This ensures stack-relative access is consistent with PUSH/POP.

## 4.6 Constraints

- Maximum program size: 232 bytes (code + data + stack share 0x00-0xE7); addresses 232-255 are I/O and will be overwritten if program exceeds 232 bytes
- Data storage: 64 KB via DP register (256 pages × 256 bytes); see [memory model](isa.md#13-memory-model)
- All immediate values must fit in one byte (0-255)
- Mnemonics are case-insensitive (`mov` = `MOV` = `Mov`)
- DB with string operand generates one byte per character (ASCII codes)
- DB is not recorded in the instruction mapping (not a CPU instruction)

## 4.7 Error Handling

All errors include the source line number.

| Error | Trigger |
|-------|---------|
| `Duplicate label: X` | Label defined more than once (case-insensitive) |
| `Label contains keyword: X` | Label name is A, B, C, D, SP, or DP |
| `Undefined label: X` | Label used but never defined (detected in pass 2) |
| `Invalid number format` | Number doesn't match any supported format |
| `X must have a value between 0-255` | Number out of byte range |
| `offset must be a value between -16...+15` | Register indirect offset out of range |
| `Only one character is allowed` | Character literal has more than one char |
| `X does not support this operand(s)` | Invalid operand type for instruction |
| `X: too many arguments` | Extra operand for single-operand instruction |
| `DB does not support this operand` | Invalid operand for DB directive |
| `Invalid instruction: X` | Unknown mnemonic |
| `Syntax error` | Line cannot be parsed |
