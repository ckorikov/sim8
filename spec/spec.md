# Technical Specification Document

## 8-bit CPU Simulator

**Reference Implementation:** [Schweigi/assembler-simulator](https://github.com/Schweigi/assembler-simulator)
**Target Platform:** Modern Web Browsers
**Purpose:** Educational tool for assembly language learning

**Architecture Version:** 2

---

## Table of Contents

| Section | File |
|---------|------|
| [1. Instruction Set Architecture (ISA)](isa.md) | `isa.md` |
| [2. Memory Model & Addressing](mem.md) | `mem.md` |
| [3. CPU Architecture](cpu.md) | `cpu.md` |
| [4. Microarchitecture: Interpreter Model](uarch.md) | `uarch.md` |
| [5. Assembler Specification](asm.md) | `asm.md` |
| [6. Test Specification](tests.md) | `tests.md` |
| [7. Floating-Point Unit (FPU)](fp.md) | `fp.md` |
| [8. FP Test Specification](tests-fp.md) | `tests-fp.md` |
| [Appendix A: Complete Opcode Table](opcodes.md) | `opcodes.md` |
| [Appendix B: Error Codes](errors.md) | `errors.md` |

---

## Version History

### v0 — Schweigi/assembler-simulator (baseline)

Original 8-bit CPU simulator by Marco Schweighauser. Single-page web app (JavaScript/AngularJS). 256-byte flat memory, 4 GPR (A-D) + SP, no formal specification.

- **GitHub:** <https://github.com/Schweigi/assembler-simulator>
- **Demo:** <https://schweigi.github.io/assembler-simulator/>

### v1 — sim8

Redesigned architecture with formal specification and verification. Key changes from v0:

**Memory model — 64 KB paged address space:**

- 256 pages × 256 bytes (was 256 bytes flat)
- New **DP register** (Data Page, code 5) selects active page for data access
- IP/stack/jumps remain page-0 only; DP affects `[addr]` and `[reg±offset]` for GPRs
- Memory-mapped console I/O: page 0, offsets 232-255 (24 characters)

**ISA changes:**

- **DB with lists:** `DB 1, 2, 3` — comma-separated byte lists (v0 supported only single values and strings)
- **Bitwise carry cleared:** AND/OR/XOR/NOT set C=0 (v0 left C unchanged)
- **Register constraints tightened:** DP allowed only in MOV; SP disallowed in bitwise/shift/MUL/DIV/jumps — violations cause FAULT(4)
- **Shift by 0:** C unchanged, Z recomputed (formally verified)

**Formal FAULT state machine:**

- CPU states: IDLE → RUNNING → HALTED / FAULT (was exception-based)
- 6 named error codes (ERR_DIV_ZERO through ERR_INVALID_OPCODE) stored in register A
- Pre-check validation: faults fire before any state modification (atomicity)
- Z and C flags preserved across faults

**Bug fixes from v0:**

- Stack bounds checked **before** write/read (v0 checked after)
- IP overflow: explicit `IP + instrLen >= 256` → FAULT(5) (v0 had generic "IP outside memory")
- CALL return address wraps mod 256 when `IP + 2 > 255`

**Cost model (new):**

- Pipeline stages: register/ALU (1 tick), memory (2 ticks), expensive ALU — MUL/DIV (2 ticks)
- Independent stages: cost = max (parallel). Data dependency: cost = sum (sequential)
- 5 cost levels: 0 (HLT), 1 (reg-only/jumps), 2 (memory/stack/MUL reg), 3 (ALU+memory), 4 (mem+mem or MUL/DIV+memory)
- Counters: `steps` (instructions) and `cycles` (ticks); neither incremented on HLT or FAULT
- Configurable per-mnemonic overrides: `CPU(costs={"MUL": 8})`

**Formal verification (new):**

- TLA+ model (`formal/`) — executable specification of all 74 opcodes
- TLC model checker: 30+ test suites covering arithmetic, shifts, bitwise, stack, memory, faults, cost model
- Spec-driven workflow: `spec/` → `formal/` → implementation → tests

**Toolchain (new):**

- Python implementation (pysim8): assembler, TUI simulator, disassembler
- Two-pass assembler with forward label resolution, strict validation
- Terminal TUI (Rich): scrolling trace, register panel, I/O display, playback control
- MCP server for LLM integration (Claude Code / Claude Desktop)

### v2 — sim8 FPU extension (current)

IEEE 754 floating-point coprocessor extension. Key additions from v1:

**FP Register Model:**

- One 32-bit physical FP register with 15 named sub-register views (FA, FHA/FHB, FQA-FQD, FOA-FOH)
- x86-style aliasing: writing a wider view overwrites all contained narrower views
- Encoding reserves up to 4 physical registers; v2 implements 1

**FP Formats (EXMY notation):**

- 5 active formats: float32 (E8M23), float16 (E5M10), bfloat16 (E8M7), OFP8 (E4M3, E5M2)
- 2 permanently reserved formats: 4-bit (E2M1, E1M2) — sub-byte, incompatible with byte-addressable memory
- Full IEEE 754 compliance: NaN propagation, ±Inf, denormals, signed zero
- E4M3: no Infinity representation (per OCP MX spec); overflow saturates to ±max finite (448)

**FP Control:**

- FPCR (8-bit): rounding mode (RNE/RTZ/RDN/RUP); bits [7:2] reserved
- FPSR (8-bit): 5 sticky IEEE 754 exception flags
- FP arithmetic exceptions always set FPSR sticky flags and produce IEEE 754 default results (no traps)

**FP Instructions (32 opcodes, 128-160 except 145):**

- Data movement: FMOV load/store (4 opcodes)
- Arithmetic: FADD, FSUB, FMUL, FDIV — memory (8 opcodes) + reg-reg (4 opcodes)
- Compare: FCMP — memory (2 opcodes) + reg-reg (1 opcode)
- Unary: FABS, FNEG, FSQRT (3 opcodes)
- Classification: FCLASS (1 opcode)
- Fused multiply-add: FMADD direct + indirect (2 opcodes, first 4-byte instruction)
- Conversion: FCVT (format-to-format), FITOF (uint8→FP), FFTOI (FP→uint8 saturating)
- Control: FSTAT, FCFG, FSCFG, FCLR (4 opcodes)

**FPM Byte Encoding:**

- 1-byte modifier (3+3+2 bits: fmt+pos+phys) for all FP data instructions
- 32 opcodes cover all formats and sub-registers (vs 80+ with per-format opcodes)

**Assembly Syntax:**

- Mandatory format suffix: `FADD.F FA, [addr]` (short) or `FADD.E8M23 FA, [addr]` (EXMY alias)
- Assembler validates suffix width matches register width
- FCVT uses dual suffix: `FCVT.H.F FHA, FA`
- Reg-reg: `FADD.H FHA, FHB` (no brackets = register), FMADD: `FMADD.H FHA, FHB, [addr]`

**New FAULT code:**

- ERR_FP_FORMAT (12): always FAULT (invalid FPM byte encoding)

**Cost model extension:**

- FP unary: 3 ticks, FCLASS: 2 ticks, FSQRT: 4 ticks, FP move: 2 ticks
- FP binary + mem: 5 ticks, FP reg-reg: 3 ticks, FMADD: 6 ticks
- FP conversion: 3 ticks, FP control: 1 tick

**Totals:** 108 opcodes assigned (74 integer + 34 FP), 148 free, 7 error codes
