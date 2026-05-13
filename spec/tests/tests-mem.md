# Memory Model Test Specification

> Architecture v3 | Part of [Technical Specification](../spec.md) | See also: [Memory Model](../mem.md), [ISA](../isa.md), [CPU Tests](tests-cpu.md), [Display Tests](tests-io-display.md), [UART Tests](tests-io-uart.md), [VU Tests](tests-vu.md)

## Scope

Tests in this file cover **mem.md** behaviors not already verified elsewhere:

- Memory initialization
- FP multi-byte memory access (byte ordering, page boundary)
- VU memory model (addressing, byte ordering, OOB behavior via VU commands)
- Stack addressing edge cases not in tests-cpu.md

**Not duplicated here** (covered by domain test files):
- DP paged addressing, page boundary violation, indirect addressing: [tests-cpu.md §6.21](tests-cpu.md)
- Display cells (0xE8–0xFB): [tests-io-display.md](tests-io-display.md)
- UART ports (0xFC–0xFF): [tests-io-uart.md](tests-io-uart.md)
- VU OOB faults: [tests-vu.md §10.14.2](tests-vu.md)
- FP page boundary fault: [tests-fp.md]

---

## Methodology

| Target | Description |
|--------|-------------|
| `mem[addr]` | Memory byte at absolute address |
| `F`, `A` | Fault flag and error code |

---

## M.1 Memory Initialization

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| M10 | `MOV A, [0x10]; HLT` (no prior write at 0x10) | A=0 | Page 0 non-code region initialized to 0 |
| M11 | `MOV DP, 5; MOV A, [0]; HLT` | A=0 | Extended memory page initialized to 0 |

---

## M.2 FP Memory Access — Byte Ordering

FP values stored in memory are **little-endian** (LSB at lowest address).

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| M12 | `FMOV.F FA, [data]; HLT` | FA = 1.0f | Load f32 LE: [0x00,0x00,0x80,0x3F] |
|      | `data: DB 0x00,0x00,0x80,0x3F` | | |
| M13 | `FMOV.F FA, [data]; FMOV.F [out], FA; HLT` | mem[out..out+3] = [0x00,0x00,0x80,0x3F] | Store f32 LE |
|      | `data: DB 0x00,0x00,0x80,0x3F` | | |
| M14 | `FMOV.H FHA, [data]; HLT` | FHA = 1.0_h | Load f16 LE: [0x00,0x3C] |
|      | `data: DB 0x00,0x3C` | | |
| M15 | `FMOV.BF FHA, [data]; HLT` | FHA = 1.0_bf | Load bf16 LE: [0x80,0x3F] |
|      | `data: DB 0x80,0x3F` | | |

### M.2.1 FP Page Boundary — Multi-Byte Access

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| M16 | `MOV A, 254; FMOV.F FA, [A]; HLT` | F=1, A=5 (ERR_PAGE_BOUNDARY) | f32 at offset 254: bytes 254–257 → OOB |
| M17 | `MOV A, 255; FMOV.H FHA, [A]; HLT` | F=1, A=5 | f16 at offset 255: byte 255 OK but byte 256 OOB |

---

## M.3 VU Memory Model

VU uses absolute 16-bit addresses (DP ignored). Tests verify the addressing model, not VU arithmetic (covered in tests-vu.md).

### M.3.1 Absolute Addressing — DP Ignored

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| M18 | `MOV DP, 5` | mem[0x0200..] updated | VU writes to absolute addr, not DP-relative |
|      | `VSET VA, 2, 0; VSET VC, 2, 0` | | VA=0x0200 absolute |
|      | `VSET VL, 0, 4; VADD.U VC, VA, 1` | | |
|      | `VWAIT; HLT` | | |

### M.3.2 VU Cross-Page Access

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| M19 | VU writes VL elements crossing page boundary (e.g., VA=0x00FE, VL=4, fmt=.U) | no FAULT, mem[0x0100..] written | VU uses full 16-bit addr space |
|      | `VSET VA, 0, 0xFE; VSET VC, 0, 0xFE` | mem[0xFE..0x101] = [src+1]×4 | |
|      | `VSET VL, 0, 4; VADD.U VC, VA, 1; VWAIT; HLT` | | |

### M.3.3 VU Byte Ordering

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| M20 | `; VA points to [0x00,0x3C] (f16(1.0) LE)` | mem[VC₀..] = f16(1.0) LE | VU stores f16 LE |
|      | `VSET VL, 0, 1; VMOV.H VC, VA; VWAIT; HLT` | mem[VC₀]=0x00, mem[VC₀+1]=0x3C | |

---

## M.4 Stack Addressing

Stack addressing is always page 0, regardless of DP.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| M21 | `MOV DP, 2; MOV A, 42; PUSH A; POP B; HLT` | B=42 | Stack on page 0 even with DP=2 |
| M22 | `MOV A, 42; PUSH A; MOV A, [SP+1]; HLT` | A=42 | SP-relative always page 0 |
| M23 | `MOV DP, 3; MOV A, [SP]; HLT` | A=mem[SP] on page 0 | SP indirect ignores DP |
