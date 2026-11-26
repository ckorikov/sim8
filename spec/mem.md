# 2. Memory Model & Addressing

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [CPU Architecture](cpu.md), [Microarchitecture](uarch.md), [Assembler](asm.md), [Tests](tests.md), [FP Tests](tests-fp.md), [FPU](fp.md)

This document is a focused reference for **memory layout**, **paged addressing via DP**, and **effective address calculation**.

## Overview

- Total address space: **64 KB** = 256 pages × 256 bytes
- Bytes are 0–255; all addresses are integers
- Program execution (IP) is **page 0 only**

## Page 0 Layout (0x0000–0x00FF)

Page 0 is special: it contains **code**, **stack**, and the **console I/O window**.

| Region | Offsets | Size | Notes |
| --- | ---: | ---: | --- |
| General page-0 area | 0x00–0xE7 | 232 | Code/data/stack share this region |
| Console output (I/O) | 0xE8–0xFF | 24 | Memory-mapped display cells |

**Program size constraint:** code executed by IP must fit in **0x00–0xE7** (232 bytes). Writing beyond 0xE7 overwrites the console window.

## DP (Data Page) and Paged Memory

`DP` selects which 256-byte page is used for *data* addressing.

- Valid DP values: 0–255
- Default at reset: DP=0
- DP affects:
  - direct `[addr]` where `addr` is 0–255
  - register indirect `[reg±offset]` for A/B/C/D
- DP does **not** affect:
  - instruction fetch (IP)
  - jumps/CALL/RET targets (page-0 offsets)
  - stack location (always on page 0)
  - SP-relative addressing (`[SP±offset]`, always page 0)

## I/O (Memory-Mapped Console)

The simulator exposes a simple character display as a **memory-mapped I/O window**.

- Location: **page 0 only**, offsets **232–255** (0xE8–0xFF)
- Capacity: **24 characters**, left-to-right in increasing address order
- Readable and writable like normal memory

### DP interaction (important)

The console window exists **only on page 0**.

- To access the display, software must use `DP=0` and addresses `[232]..[255]`.
- When `DP≠0`, `[232]..[255]` access normal data memory on that page, not the console.

### Display semantics

- Each byte is interpreted as an ASCII character code for display.
- Non-printable and whitespace characters display as blank space.
- On reset, the I/O window displays as blanks.

## Effective Address Calculation

### Direct addressing: `[addr]`

- Operand `addr` is an 8-bit offset 0–255
- Effective address:

$$\text{EA} = DP \times 256 + addr$$

### Register indirect addressing: `[reg±offset]`

Encoding uses a single byte: low 3 bits = register code; high 5 bits = signed offset −16..+15.

- If `reg` is A/B/C/D:

$$\text{pageOffset} = regValue + offset$$
$$\text{EA} = DP \times 256 + \text{pageOffset}$$

- If `reg` is SP:

$$\text{pageOffset} = SP + offset$$
$$\text{EA} = \text{pageOffset} \quad (\text{page 0 only})$$

**Page boundary rule:** if `pageOffset` is outside 0–255, the CPU enters FAULT with `ERR_PAGE_BOUNDARY` (i.e., `F=true` and `A=5`; see [Error Codes](errors.md)).

## Stack Addressing

- Stack pointer initial value: SP=0xE7 (231)
- Stack resides on **page 0**
- PUSH/POP/CALL/RET perform bounds checking and enter **FAULT (A=2/A=3)** on underflow/overflow (see [Error Codes](errors.md))
- Arithmetic that manually modifies SP via MOV/ADD/SUB/INC/DEC does **not** perform bounds checking
- **PUSH source and DP:** `PUSH [addr]` and `PUSH [reg]` read the source value using DP (effective address = `DP × 256 + offset`), but always write to the stack on page 0. This is asymmetric by design — DP affects where data is *read from*, not where the stack resides.

## FP Memory Access

FP instructions (FMOV, FADD, FSUB, FMUL, FDIV, FCMP) access multi-byte values in memory. All FP memory access follows the same DP-based addressing as integer instructions.

### Byte Ordering

FP values are stored in **little-endian** byte order (least significant byte at lowest address).

**Example:** float32 `1.0` = `0x3F800000` is stored as:

| Address | Byte |
|---------|------|
| EA + 0  | 0x00 |
| EA + 1  | 0x00 |
| EA + 2  | 0x80 |
| EA + 3  | 0x3F |

### Effective Address

FP instructions use the same effective address calculation as integer instructions:

- Direct: `EA = DP × 256 + addr`
- Register indirect: `EA = DP × 256 + reg_value + offset` (SP-relative uses page 0)

### Page Boundary Constraint

An FP memory access must not cross a page boundary. If `page_offset + size - 1 > 255`, the CPU enters FAULT with `ERR_PAGE_BOUNDARY` (A=5).

| Format width | Bytes | Max page_offset | Constraint |
|-------------|-------|-----------------|------------|
| 32-bit (.F) | 4 | 252 | addr ≤ 252 |
| 16-bit (.H, .BF) | 2 | 254 | addr ≤ 254 |
| 8-bit (.O3, .O2) | 1 | 255 | No additional constraint (single byte) |

**Note on 4-bit formats:** 4-bit formats (.N1, .N2) are permanently reserved in v2. They are sub-byte (4 bits) and fundamentally incompatible with the byte-addressable memory model — the smallest addressable memory unit is 8 bits. FOA-FOH sub-register views are accessible only through aliasing (writing to a wider view that contains them). Any FP instruction using fmt ≥ 5 triggers FAULT(`ERR_FP_FORMAT`) at decode. See [FPU](fp.md#72-fp-register-model).

### Atomicity

FP memory reads and writes are not atomic with respect to interrupts (sim8 has no interrupt model). A multi-byte read fetches bytes sequentially from low to high address. A multi-byte write stores bytes sequentially from low to high address.

## Conformance Notes

- Effective address calculation must be consistent across all instructions that access memory (see [Microarchitecture](uarch.md) for the interpreter-model pseudocode).
- Conformance tests rely on:
  - DP affecting both `[addr]` and `[reg±offset]` for A/B/C/D
  - SP-relative ignoring DP
  - I/O being reachable only when DP=0
