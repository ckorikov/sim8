# Pad Test Specification

> Architecture v3 | Part of [Technical Specification](../spec.md) | See also: [I/O Pad](../io-pad.md), [Memory Model](../mem.md), [Display Tests](tests-io-display.md)

## Scope

Tests in this file cover the **pixel pad** memory mapping:

- Memory layout (row-major, byte per pixel)
- CPU read/write round-trip
- VU bulk writes to pad region
- Boundary and sizing behavior

---

## Methodology

| Target | Description |
|--------|-------------|
| `pad[r][c]` | Pixel at row r, column c (0-based) |
| `mem[addr]` | Memory byte at absolute address |
| `padStart` | Absolute start address = page × 256 + offset |

Tests assume pad configured at page=1, offset=0 (padStart=0x0100) unless otherwise stated.

---

## P.1 Memory Layout

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| P1 | `MOV DP, 1; MOV [0], 255; HLT` | pad[0][0]=255, mem[0x0100]=255 | First pixel = padStart+0 |
| P2 | `MOV DP, 1; MOV [28], 255; HLT` (28×28 grid) | pad[1][0]=255, mem[0x011C]=255 | First pixel of row 1 = padStart+size |
| P3 | `MOV DP, 1; MOV [783], 255; HLT` (28×28) | pad[27][27]=255, mem[0x0100+783]=255 | Last pixel = padStart+size²−1 |

---

## P.2 Pixel Encoding

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| P4 | Write 0 to pad cell | pad[r][c] = 0 (empty/background) | Value 0 = background |
| P5 | Write 255 to pad cell | pad[r][c] = 255 (filled) | Value 255 = full foreground |
| P6 | Write 128 to pad cell | pad[r][c] = 128 (half-brightness) | Mid values = partial fill |

---

## P.3 CPU Read/Write Round-Trip

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| P7 | `MOV DP, 1; MOV [0], 200; MOV A, [0]; HLT` | A=200 | Pad memory readable as normal memory |
| P8 | `MOV DP, 1; MOV [0], 255; MOV [0], 0; HLT` | pad[0][0]=0 | Overwrite clears pixel |

---

## P.4 VU Bulk Write

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| P9 | `VSET VA, 1, 0; VSET VL, 0, 28*28; VFILL.U VC, 255; VWAIT; HLT` | all 784 pad cells = 255 | VFILL fills entire 28×28 pad |
| P10 | `VSET VA, 1, 0; VSET VC, 1, 0; VSET VL, 0, 28; VFILL.U VC, 0; VWAIT; HLT` | pad row 0 = 0 | Clear top row |

---

## P.5 Notes

Tests to be written for:

- Pad configured at non-default page/offset
- Pad configured with different grid sizes (8, 16, 64)
- Simultaneous CPU and VU access (undefined behavior — simulator behavior may differ from spec)
