# 5. Assembler Specification

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [Instruction Encoding](isa.md#18-instruction-encoding-format), [FPU](fp.md)

## 5.1 Assembly Pipeline

Assembly proceeds in three phases:

**Phase 0 — Preprocessing:**

Recursively resolve all `@include` directives (see §5.8), producing an ordered sequence of source lines each annotated with its origin `(filename, line_no)`. `@include` directive lines themselves are consumed and do not appear in this sequence. The two-pass assembler operates on this annotated sequence; it never sees `@include` directives.

**Pass 1 — Code Generation:**

For each source line:

1. Parse an optional label, mnemonic, and operands.
1. If a label is present, record its address as the current output position.
1. If a mnemonic is present, determine the opcode from the mnemonic + operand types and emit opcode + operand bytes.
1. Record a source mapping (output position → `(filename, line_no)`) for diagnostics.
1. If the line is neither a label, instruction, blank, nor comment → syntax error.

Forward label references may be left unresolved during pass 1.

**Pass 2 — Label Resolution:**

Resolve all label references in operands to their numeric addresses. If a label is not found, report an "Undefined label" error.

## 5.2 Assembler Output

The assembler produces:

- Machine code as a sequence of bytes (each 0–255)
- A label table (label name → address)
- A source mapping (output position → source location, 1-based) for diagnostics. A source location is `(filename, line_no)` where `filename` is normalized relative to the root file's directory (see §5.8 Error reporting for normalization rules)

**Note:** DB pseudo-instructions and `@include` directive lines are not CPU instructions and are excluded from source-to-instruction mapping. DB entries are excluded because they are data, not instructions. `@include` lines are excluded because they are consumed in Phase 0 and never reach Pass 1.

## 5.3 Labels

- Defined with trailing colon: `start:`, `.loop:`
- Must start with a letter or dot, followed by word characters: `/^[.A-Za-z]\w*$/`
- Case-insensitive duplicate detection (`Start` and `start` are the same label)
- Forbidden names: `A`, `B`, `C`, `D`, `SP`, `DP`, `FA`, `FB`, `FC`, `FD`, `FHA`, `FHB`, `FHC`, `FHD`, `FHE`, `FHF`, `FHG`, `FHH`, `FQA`, `FQB`, `FQC`, `FQD`, `FQE`, `FQF`, `FQG`, `FQH`, `FQI`, `FQJ`, `FQK`, `FQL`, `FQM`, `FQN`, `FQO`, `FQP`, `FOA`, `FOB`, `FOC`, `FOD`, `FOE`, `FOF`, `FOG`, `FOH`, `FOI`, `FOJ`, `FOK`, `FOL`, `FOM`, `FON`, `FOO`, `FOP` (conflict with register names; `FC`/`FD` and phys 2-3 sub-register names are reserved for future expansion)
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

| Register | Width | Phys | Description |
|----------|-------|------|-------------|
| FA | 32-bit | 0 | Full FP register |
| FB | 32-bit | 1 | Full FP register |
| FHA, FHB | 16-bit | 0 | Half views (low, high) |
| FHC, FHD | 16-bit | 1 | Half views (low, high) |
| FQA, FQB, FQC, FQD | 8-bit | 0 | Quarter views |
| FQE, FQF, FQG, FQH | 8-bit | 1 | Quarter views |
| FOA-FOH | 4-bit | 0 | Octet views (reserved in v2 ops) |
| FOI-FOP | 4-bit | 1 | Octet views (reserved in v2 ops) |

FP registers are used with FP instructions only (opcodes 128-162). FP register names are case-insensitive: `FA` = `fa` = `Fa`.

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

- `.F` (32-bit) → FA, FB
- `.H`, `.BF` (16-bit) → FHA, FHB, FHC, FHD
- `.O3`, `.O2` (8-bit) → FQA–FQH
- `.N1`, `.N2` (4-bit) → FOA–FOP

A mismatch is an assembler error (e.g., `FADD.F FHA, [0]` → error).

### FMOV Register-to-Register

FMOV with two FP register operands (no brackets) is a raw bit copy (opcode 145):

```
FMOV.H FHA, FHB      ; raw bit copy FHB → FHA
FMOV.F FA, FB         ; raw bit copy FB → FA
```

Both operands must have the same format suffix. Position and physical register may differ. This is distinct from memory-variant FMOV (brackets = memory) and should be used instead of same-format FCVT.

### FCVT Dual Suffix

FCVT uses two suffixes: `FCVT.dst_fmt.src_fmt dst_reg, src_reg`.

Example: `FCVT.H.F FHA, FA` — convert float32 in FA to float16 in FHA.

**Same-format restriction:** The assembler rejects `FCVT` when both suffixes specify the same format (e.g., `FCVT.H.H FHA, FHB`). Use `FMOV` for same-format register copies instead.

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

### FMOV with FP Immediate

FMOV supports loading an FP literal directly into a sub-register for OFP8 and 16-bit formats:

```asm
FMOV.O3 FQA, 1.5        ; OFP8 E4M3 immediate (3 bytes)
FMOV.O2 FQB, -0.5       ; OFP8 E5M2 immediate (3 bytes)
FMOV.H  FHA, 3.14       ; float16 immediate (4 bytes)
FMOV.BF FHB, 2.0        ; bfloat16 immediate (4 bytes)
```

The literal uses the same syntax as DB float literals. An optional suffix on the literal must match the instruction suffix:

```asm
FMOV.O3 FQA, 1.5_o3     ; OK (explicit suffix matches)
FMOV.O3 FQA, 1.5_h      ; ERROR: FP immediate suffix mismatch
```

Float32 immediate is not supported — it would exceed the 4-byte maximum instruction length. Use `DB` + `[label]` instead:

```asm
FMOV.F FA, 1.0           ; ERROR: FP immediate not supported for float32
```

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

## 5.8 Include Directive

The `@include` directive substitutes the contents of another source file in place before assembly begins. This enables sharing common routines (e.g., print helpers, page-swap utilities) across multiple programs, and is the mechanism for expressing inter-file dependencies portably — both in CLI and IDE environments.

**Syntax:**

```
@include "path/to/file.asm"
@include "https://example.com/lib.asm"
```

The directive must occupy its own line (leading whitespace is allowed; trailing content after the closing quote is a syntax error). The keyword `@include` is case-insensitive (`@INCLUDE`, `@Include` are equivalent). The path is a string literal (double quotes); an empty path is a syntax error. Path resolution is environment-specific, but follows the same semantics in all environments: each path is resolved relative to the directory of the file containing the `@include` directive. Specific cases:

- **CLI file input:** relative to the directory of the root `.asm` file.
- **CLI stdin:** relative to CWD.
- **IDE virtual filesystem:** relative to the virtual directory of the including file — not the virtual root.
- **In-memory string (e.g., MCP `assemble_source`):** `@include` is not supported; using it is an assembler error (`@include: no filesystem context`).

Escape sequences in the path are not supported.

**Semantics:** Logically equivalent to inlining the file's contents at that point — the directive is replaced by the included file's lines before assembly begins. The preprocessor always inserts a line boundary after the last line of an included file, so a missing trailing newline in the included file does not cause its last line to merge with the first line following the directive. Origin tracking (file + line) is preserved throughout so that diagnostics refer to the original source location, not a merged line number. The resulting unified source is passed through the normal two-pass assembler (§5.1). There is no separate compilation or linking step.

**Nesting:** Included files may themselves contain `@include` directives. Maximum include depth: 16 levels.

**Circular includes:** If a file directly or indirectly includes itself, it is an assembler error. Detection is based on the canonical normalized path of each file, not the literal string in the directive — so `lib/print.asm` and `./lib/../lib/print.asm` are treated as the same file. On real filesystems, canonical path means the OS-level absolute path (symlinks resolved). In virtual filesystems (IDE), canonical path means the normalized virtual path.

**Namespace:** All labels from included files share the same flat namespace. Duplicate labels across files are an error (same rules as §5.3).

**Error reporting:** All errors include a source location as `filename:line` (1-based). `filename` is the path of each file normalized to be relative to the root file's directory (or an absolute path if the file is outside that directory tree). For the root file, `filename` is its own name (or `<stdin>`). This format is used consistently regardless of whether any `@include` directives are present.

**Binary files:** If the included file is not valid UTF-8, it is treated as a raw binary blob. Its bytes are embedded at the include point as if the source contained `DB b0, b1, ..., bn` (a single data directive with all byte values). Empty binary files are silently skipped. The source-location entry in the line map for the emitted data refers to the `@include` directive's own file and line. Binary files are not scanned for nested `@include` directives.

**URL includes:** The path in an `@include` directive may be an absolute HTTP or HTTPS URL (must start with `http://` or `https://`). URL includes are fetched at assemble time before the two-pass assembly begins. The same binary detection rule applies: if the response body is not valid UTF-8, it is embedded as `DB` bytes. Relative paths inside a URL-fetched file are not supported (only absolute URLs or, in CLI mode, absolute filesystem paths). Circular URL detection uses the URL string directly. The error `@include: fetch failed: X` is raised if the fetch fails for any reason (network error, non-2xx status, etc.).

**No include guards:** The assembler does not prevent multiple inclusion of the same file. Repeated inclusion duplicates its contents, which will typically cause `Duplicate label` errors. This is by design — include guards are the responsibility of the author.

## 5.9 Error Handling

All errors include a source location in `filename:line` format (1-based line number). See §5.8 for details on filename resolution.

| Error | Trigger |
|-------|---------|
| `Duplicate label: X` | Label defined more than once (case-insensitive) |
| `Label contains keyword: X` | Label name is a register name or reserved FP name (see forbidden names in §5.3) |
| `Undefined label: X` | Label used but never defined (detected in pass 2) |
| `Invalid number format` | Number doesn't match any supported format |
| `X must have a value between 0-255` | Number out of byte range |
| `offset must be a value between -16...+15` | Register indirect offset out of range |
| `Invalid register in address: X` | Unknown register name inside `[reg±offset]` address |
| `Invalid address: X` | Address expression cannot be parsed |
| `Only one character is allowed` | Character literal has more than one char |
| `Invalid operand: X` | Token in operand position is not a valid register, number, address, or literal |
| `X does not support this operand(s)` | Invalid operand type for instruction |
| `X: too many arguments` | Extra operand for single-operand instruction |
| `DB does not support this operand` | Invalid operand for DB directive |
| `Invalid instruction: X` | Unknown mnemonic |
| `Syntax error` | Line cannot be parsed |
| `FP format suffix required` | FP data instruction used without suffix (e.g., `FADD FA, [0]`) |
| `FP format suffix does not match register width` | Suffix width ≠ register width (e.g., `.F` + `FHA`) |
| `Invalid FP format suffix: X` | Unknown suffix (not .F/.H/.BF/.O3/.O2/.N1/.N2 or EXMY alias) |
| `Invalid FP register: X` | Unknown FP register name |
| `FMOV does not support this operand(s)` | FMOV operand combination is not register-to-register, memory, or immediate |
| `DB does not support mixing float and integer operands` | Float and integer/string operands in one DB |
| `Unsupported float format for DB: X` | 4-bit format suffix (`_n1`, `_n2`, `_e2m1`, `_e1m2`) used in DB |
| `Float value out of range for format E4M3` | OFP8 E4M3 value overflows max finite (448); E4M3 has no Infinity representation |
| `Invalid float literal` | Malformed float syntax in DB |
| `FP immediate not supported for float32` | FMOV.F with immediate operand |
| `FP immediate not supported for 4-bit formats` | FMOV with 4-bit format (`.N1`/`.N2`) and immediate operand |
| `DB string must not be empty` | `DB ""` — empty string literal |
| `FP immediate suffix mismatch` | Literal suffix does not match instruction suffix |
| `FCVT with identical formats (use FMOV)` | FCVT dst and src formats are the same |
| `@include: no filesystem context` | `@include` used when assembling from an in-memory string (no file path available) |
| `@include: invalid syntax` | Malformed `@include` directive (missing quotes, extra tokens, empty path) |
| `@include: file not found: X` | Named file does not exist |
| `@include: circular include: X` | File X is already in the include chain |
| `@include: max include depth exceeded` | Include nesting exceeds 16 levels |
| `@include: fetch failed: X` | URL fetch failed (network error, non-2xx response, etc.) |
