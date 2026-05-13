# I/O: Pixel Pad

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [Memory Model](mem.md), [I/O Display](io-display.md), [Pad Tests](tests/tests-io-pad.md)

## Overview

The pixel pad is a configurable memory-mapped pixel grid. It maps a contiguous region of the 64 KB address space to an N×N visual canvas in the simulator UI. The mapping is bidirectional: CPU writes to the region update the visual, and mouse input on the canvas writes to memory.

The pad has no fixed hardware address — its location (page and offset) and grid size are configurable at runtime in the simulator UI.

---

## State

The pad's location and size are runtime configuration, not architectural state:

| Parameter | Values | Notes |
|-----------|--------|-------|
| `page` | 0–255 | Page number of the pad start address |
| `offset` | 0–255 | Byte offset within the page |
| `size` | 8, 16, 28, 64 | Grid side length in pixels |

The pad occupies `size × size` consecutive bytes starting at absolute address `page × 256 + offset`. The total must not exceed 0xFFFF.

---

## Properties

### Memory Layout

Pixels are laid out in **row-major order**:

- Row 0: bytes 0..(size−1)
- Row 1: bytes size..(2×size−1)
- ...
- Row (size−1): bytes ((size−1)×size)..(size²−1)

Byte at row `r`, column `c` → absolute address `page × 256 + offset + r × size + c`.

### Pixel Encoding

Each byte encodes one pixel:

| Value | Meaning |
|-------|---------|
| 0 | Empty / background |
| 1–254 | Filled (brightness proportional to value in UI) |
| 255 | Fully filled / foreground |

Mouse drawing writes 255 to the selected cell. Programs may write any value 0–255.

### Bidirectional Sync

- CPU or VU writes to the pad memory region → canvas updates immediately after each instruction step
- Mouse draw on canvas → writes 255 to the corresponding memory byte → visible to CPU on next read

### DP Interaction

The pad uses the **absolute 16-bit address** `page × 256 + offset`. CPU access must account for DP:

- To write to the pad from CPU, set `DP = page` and use offset-based addressing, or keep `DP = 0` and place the pad on page 0
- VU operations use absolute addresses directly, ignoring DP — suitable for high-throughput pixel writes

---

## Instructions

No dedicated instructions. Programs access the pad region using standard memory instructions or VU commands (e.g., `VFILL`, `VMOV`, `VADD`).

---

## Faults

No pad-specific faults. Address range validity follows standard CPU/VU memory rules:

- CPU: `ERR_PAGE_BOUNDARY` if access crosses a page boundary
- VU: `ERR_VU_OOB` if absolute address + length exceeds 0xFFFF

---

## Notes

- The pad is a simulator visualization tool, not a hardware peripheral; it has no real-world ISA analogue
- Default configuration at simulator startup: page 1, offset 0, size 28×28
- Setting `page = 0, offset = 0` places the pad over code/stack — valid but typically avoided
