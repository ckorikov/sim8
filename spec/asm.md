# 5. Assembler Specification

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [Instruction Encoding](isa.md#18-instruction-encoding-format), [FPU](fp.md)

## 5.1 Two-Pass Assembly

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

## 5.2 Assembler Output

The assembler produces:

- Machine code as a sequence of bytes (each 0–255)
- A label table (label name → address)
- A source mapping (output position → source line number, 1-based) for diagnostics

**Note:** DB pseudo-instructions are not CPU instructions and may be excluded from source-to-instruction mapping.

## 5.3 Labels

- Defined with trailing colon: `start:`, `.loop:`
- Must start with a letter or dot, followed by word characters: `/^[.A-Za-z]\w*$/`
- Case-insensitive duplicate detection (`Start` and `start` are the same label)
- Forbidden names: `A`, `B`, `C`, `D`, `SP`, `DP`, `FA`, `FHA`, `FHB`, `FQA`, `FQB`, `FQC`, `FQD`, `FOA`, `FOB`, `FOC`, `FOD`, `FOE`, `FOF`, `FOG`, `FOH` (conflict with register names)
- Forward references allowed — a label can be used before its definition
- Labels can be used inside brackets: `[label]` is equivalent to `[addr]` where addr is the label's resolved address. Uses the same direct addressing opcode as `[number]`
- Dot-prefix labels supported for local scope convention: `.loop`, `.end`

## 5.4 Comments

- Semicolon (`;`) begins a comment
- Standalone comment lines: `; this is a comment`
- Inline comments after instructions: `MOV A, 5 ; load value`
- Empty lines are allowed

## 5.5 Register Operands

| Register | Code | Allowed as operand |
|----------|------|-------------------|
| A, B, C, D | 0-3 | All instructions that accept registers |
| SP | 4 | MOV, ADD, SUB, INC, DEC, CMP; also as base in `[SP±offset]` |
| DP | 5 | MOV only (`MOV DP, x` or `MOV x, DP`) |

### FP Register Operands

| Register | Width | Description |
|----------|-------|-------------|
| FA | 32-bit | Full FP register |
| FHA, FHB | 16-bit | Half views (low, high) |
| FQA, FQB, FQC, FQD | 8-bit | Quarter views |
| FOA-FOH | 4-bit | Octet views |

FP registers are used with FP instructions only (opcodes 128-160, except 145). FP register names are case-insensitive: `FA` = `fa` = `Fa`.

See [FPU](fp.md) for the full register model and aliasing rules.

**DP (Data Page):** Controls which 256-byte page is accessed by all data addressing: both `[addr]` (direct) and `[reg±offset]` (indirect). It does not affect control flow (jumps/CALL/RET) or the fact that PUSH/POP always write to the stack on page 0. **Console I/O is memory-mapped on page 0**, so to access `[232]..[255]` as I/O via direct addressing, software must use `DP=0`. See [Memory Model & Addressing](mem.md).

**SP in indirect addressing:** `[SP±offset]` always uses page 0, regardless of DP. This ensures stack-relative access is consistent with PUSH/POP.

## 5.6 FP Assembly Syntax

### Format Suffixes

All FP data instructions require a **mandatory format suffix**, separated from the mnemonic by a dot. Both short and EXMY forms are accepted (assembler aliases — identical encoding):

| Short suffix | EXMY alias | Format | Width |
|-------------|------------|--------|-------|
| .F | .E8M23 | float32 | 32 |
| .H | .E5M10 | float16 | 16 |
| .BF | .E8M7 | bfloat16 | 16 |
| .O3 | .E4M3 | OFP8 | 8 |
| .O2 | .E5M2 | OFP8 | 8 |
| .N1 | .E2M1 | 4-bit | 4 |
| .N2 | .E1M2 | 4-bit | 4 |

Suffixes are case-insensitive: `.F` = `.f`, `.BF` = `.bf`.

**Pattern:** `Fop.fmt reg, operand` — e.g., `FADD.F FA, [addr]`.

Omitting the suffix on an FP data instruction is an assembler error.

**Reserved formats:** The assembler accepts suffixes `.N1` and `.N2` and generates valid machine code. However, in v2 the CPU will raise FAULT(`ERR_FP_FORMAT`) at decode time for any instruction using these 4-bit formats — they are sub-byte and incompatible with byte-addressable memory. This is by design — the assembler is format-agnostic; the CPU enforces version-specific format restrictions. Note: `.O3` and `.O2` (OFP8) are fully supported in v2.

### Suffix-Register Width Validation

The assembler validates that the suffix width matches the register width:

- `.F` (32-bit) → FA only
- `.H`, `.BF` (16-bit) → FHA, FHB only
- `.O3`, `.O2` (8-bit) → FQA, FQB, FQC, FQD only
- `.N1`, `.N2` (4-bit) → FOA-FOH only

A mismatch is an assembler error (e.g., `FADD.F FHA, [0]` → error).

### FCVT Dual Suffix

FCVT uses two suffixes: `FCVT.dst_fmt.src_fmt dst_reg, src_reg`.

Example: `FCVT.H.F FHA, FA` — convert float32 in FA to float16 in FHA.

### Register-to-Register Arithmetic

Reg-reg FP operations (153-157) use two FP register operands without memory brackets:

```
FADD.H FHA, FHB      ; reg-reg (no brackets = register operand)
FCMP.F FA, FA         ; self-compare is valid
FSUB.BF FHA, FHB      ; bfloat16 reg-reg
```

Distinction from memory variants: `FADD.H FHA, [0x50]` (brackets = memory) vs `FADD.H FHA, FHB` (no brackets = reg-reg).

Both operands must have the same format suffix. Position may differ (e.g., FHA and FHB).

### FCLASS

FCLASS classifies a FP value and writes the result mask to a GPR:

```
FCLASS.F A, FA        ; classify FA as float32, result → A
FCLASS.H B, FHB       ; classify FHB as float16, result → B
```

Operand order: `gpr, FP` (same as FFTOI).

### FMADD

FMADD is the first 4-byte instruction. It performs `dst = src × mem + dst`:

```
FMADD.H FHA, FHB, [0x50]     ; direct: FHA = FHB × mem[0x50] + FHA
FMADD.F FA, FA, [B]          ; indirect: FA = FA × mem[DP:B] + FA
```

Three operands: `dst_FP, src_FP, [mem]`. Both FP operands must have the same format suffix.

### Control Instructions

FSTAT, FCFG, FSCFG, and FCLR do not use format suffixes (they operate on control registers, not FP data).

### DB Float Literals

The `DB` directive supports floating-point literals for initializing FP data in memory.

**Literal syntax:**

```
float_literal  ::= [-+]? (digits "." digits? | "." digits) ([eE] [-+]? digits)? ("_" suffix)?
special_value  ::= [-+]? ("inf" | "nan") ("_" suffix)?
```

A literal with a decimal point (`.`) and no suffix is treated as **float32** (default format). `inf` and `nan` without a suffix are also float32.

**Suffix table:**

| Suffix | EXMY alias | Format | Bytes per value |
|--------|------------|--------|-----------------|
| `_f` (default) | `_e8m23` | float32 | 4 |
| `_h` | `_e5m10` | float16 | 2 |
| `_bf` | `_e8m7` | bfloat16 | 2 |
| `_o3` | `_e4m3` | OFP8 E4M3 | 1 |
| `_o2` | `_e5m2` | OFP8 E5M2 | 1 |

Suffixes are case-insensitive: `_F` = `_f`, `_BF` = `_bf`.

**Byte order:** little-endian (consistent with FMOV — see [FPU](fp.md)).

**Examples:**

```asm
DB 1.4              ; float32 (default), 4 bytes LE
DB 1.4_f            ; float32 explicit, 4 bytes LE
DB 1.4_h            ; float16, 2 bytes LE
DB 1.4_bf           ; bfloat16, 2 bytes LE
DB 1.4_o3           ; OFP8 E4M3, 1 byte
DB 1.4_e8m23        ; float32 (EXMY alias)
DB 1.4, 1.5, 1.6    ; array: 3 × float32 = 12 bytes
DB -1.5e2_h         ; float16 of -150.0, 2 bytes LE
DB inf_f             ; +Infinity float32, 4 bytes
DB nan_h             ; quiet NaN float16, 2 bytes
DB -inf_bf           ; -Infinity bfloat16, 2 bytes
```

**Arrays:** `DB 1.4, 1.5, 1.6` — each value is encoded independently. Different formats in one DB are allowed: `DB 1.0_f, 2.0_h` → 4 + 2 = 6 bytes.

**Overflow behavior:**

- Formats with Infinity (float32, float16, bfloat16): overflow → ±Inf.
- OFP8 E4M3 (no Inf representation): overflow → assembler error.
- OFP8 E5M2: overflow → ±Inf.

## 5.7 Constraints

- Maximum program size: 232 bytes (code + data + stack share 0x00-0xE7); addresses 232-255 are I/O and will be overwritten if program exceeds 232 bytes
- Data storage: 64 KB via DP register (256 pages × 256 bytes); see [memory model](isa.md#13-memory-model)
- All immediate values must fit in one byte (0-255)
- Mnemonics are case-insensitive (`mov` = `MOV` = `Mov`)
- DB with comma-separated operands generates one byte per value (`DB 1, 2, 3` → `[1, 2, 3]`)
- DB with string operand generates one byte per character (ASCII codes)
- DB does not support mixing strings and numbers in a single directive (`DB "A", 66` is a syntax error)
- `DB ""` (empty string) is a syntax error — DB must produce at least one byte
- Multiple distinct labels on the same address are allowed (`a: \n b: \n HLT` defines both `a` and `b` at offset 0)
- An empty program (only comments/blank lines) produces zero bytes of output and an empty label table — this is valid
- DB is not recorded in the instruction mapping (not a CPU instruction)
- DB with float literals generates N bytes per value (4 for float32, 2 for float16/bfloat16, 1 for OFP8)
- DB does not support mixing float and integer/string operands in one directive (`DB 1.4, 42` — syntax error)
- DB does not support 4-bit float formats (`_n1`, `_n2`, `_e2m1`, `_e1m2` — assembler error)
- A float literal without a suffix but with a decimal point is treated as float32
- `inf` and `nan` without a suffix are treated as float32
- Float value out of range: overflow → ±Inf for formats with Inf (F, H, BF, O2); assembler error for O3 (E4M3 has no Inf — max finite)

## 5.8 Error Handling

All errors include the source line number (1-based: first line is 1).

| Error | Trigger |
|-------|---------|
| `Duplicate label: X` | Label defined more than once (case-insensitive) |
| `Label contains keyword: X` | Label name is a register name: A, B, C, D, SP, DP, or any FP register (FA, FHA, FHB, FQA-FQD, FOA-FOH) |
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
| `FP format suffix required` | FP data instruction used without suffix (e.g., `FADD FA, [0]`) |
| `FP format suffix does not match register width` | Suffix width ≠ register width (e.g., `.F` + `FHA`) |
| `Invalid FP format suffix: X` | Unknown suffix (not .F/.H/.BF/.O3/.O2/.N1/.N2 or EXMY alias) |
| `Invalid FP register: X` | Unknown FP register name |
| `DB does not support mixing float and integer operands` | Float and integer/string operands in one DB |
| `Unsupported float format for DB: X` | 4-bit format suffix (`_n1`, `_n2`, `_e2m1`, `_e1m2`) used in DB |
| `Float value out of range for format X` | Value not representable (overflow for OFP8 E4M3) |
| `Invalid float literal` | Malformed float syntax in DB |
