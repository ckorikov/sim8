# I/O: Display

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [Memory Model](mem.md), [I/O UART](io-uart.md), [I/O Pad](io-pad.md), [Display Tests](tests/tests-io-display.md)

## Overview

The display is a 20-cell memory-mapped character output window on page 0. Each cell holds one ASCII character code and is rendered left-to-right in the simulator UI.

Active only when `DP = 0`; see [Memory Model — DP interaction](mem.md#dp-interaction-important).

---

## State

| Region | Offsets | Size | Notes |
|--------|---------|------|-------|
| Display cells | 0xE8–0xFB | 20 | Memory-mapped character output |

---

## Properties

### Character Encoding

- Each byte is interpreted as an ASCII character code
- Printable range: 32–126; values outside this range are displayed as blank
- Addresses are ordered left-to-right (cell 0 = 0xE8, cell 19 = 0xFB)

### Reset Behavior

- All display cells are initialized to 0 on reset (displayed as blanks)

### DP Interaction

Display cells require `DP = 0`. With `DP ≠ 0`, offsets 0xE8–0xFB access ordinary data memory — no display effect.

### Read Behavior

Display cells read back the current byte value, same as ordinary memory. There is no separate display-only state — the display is the memory.

---

## Instructions

No dedicated instructions. The CPU accesses display cells using standard memory instructions (`MOV`, `PUSH`, `POP`, etc.) targeting offsets 0xE8–0xFB with `DP = 0`.

---

## Faults

No display-specific faults. The display region is within the valid page-0 address range (0x00–0xFF), so no `ERR_PAGE_BOUNDARY` can occur from a direct 8-bit offset access.

---

## Notes

- The display is a visualization aid; it has no hardware analogue in the spec
- Simulators must render display cells after every instruction that writes to 0xE8–0xFB with DP = 0
- VU writes to the display region (0xE8–0xFB via absolute addresses) update the memory-mapped display, same as CPU writes
