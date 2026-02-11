# Memory Model & Addressing

> Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [CPU Architecture](cpu.md), [Microarchitecture](uarch.md), [Assembler](asm.md), [Tests](tests.md)

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

## Conformance Notes

- Effective address calculation must be consistent across all instructions that access memory (see [Microarchitecture](uarch.md) for the interpreter-model pseudocode).
- Conformance tests rely on:
  - DP affecting both `[addr]` and `[reg±offset]` for A/B/C/D
  - SP-relative ignoring DP
  - I/O being reachable only when DP=0
