# I/O: UART Terminal

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [Memory Model](mem.md), [I/O Display](io-display.md), [I/O Pad](io-pad.md), [UART Tests](tests/tests-io-uart.md)

## Overview

The UART terminal is a 4-byte memory-mapped streaming I/O port on page 0, offsets 0xFC–0xFF. It provides byte-level TX (transmit) and RX (receive) channels for terminal communication.

Active only when `DP = 0`; see [Memory Model — DP interaction](mem.md#dp-interaction-important).

---

## State

| Offset | Hex | Name | R/W | Description |
|--------|-----|------|-----|-------------|
| 252 | 0xFC | `IO_TX_DATA` | W | Write a byte → sends character to terminal output |
| 253 | 0xFD | `IO_TX_STATUS` | R | bit 0 = TX ready (always 1; reserved for baud-rate emulation) |
| 254 | 0xFE | `IO_RX_DATA` | R/W | Read = next input byte (0 if empty); write 0 to signal consumed |
| 255 | 0xFF | `IO_RX_STATUS` | R | bit 0 = input byte available |

---

## Properties

### TX Protocol

Each write to `IO_TX_DATA` (0xFC) emits exactly one byte to the terminal output, regardless of whether the value changed. The simulator clears the cell to 0 after emission.

- Reading `IO_TX_DATA` after a write returns 0 (the byte has been consumed)
- `IO_TX_STATUS` bit 0 is always 1 in v3 (TX always ready; reserved for future baud-rate emulation)

### RX Protocol

When input is available:
- `IO_RX_STATUS` (0xFF) bit 0 = 1
- `IO_RX_DATA` (0xFE) holds the next byte

After reading `IO_RX_DATA`, the program must write 0 to `IO_RX_DATA` to signal consumption. The simulator then stages the next queued byte (if any).

- If no input is pending: `IO_RX_STATUS` = 0, `IO_RX_DATA` = 0
- Without writing 0 to `IO_RX_DATA`, the same byte remains staged

### DP Interaction

UART ports require `DP = 0`. With `DP ≠ 0`, offsets 0xFC–0xFF access ordinary data memory — no UART effect.

VU writes to addresses 0x00FC–0x00FF are memory writes only; they do **not** trigger UART TX emission.

---

## Instructions

No dedicated instructions. Programs use standard CPU memory instructions (`MOV`, `AND`, `JZ`, etc.) to interact with the UART port registers.

---

## Faults

No UART-specific faults. UART registers are within the valid page-0 address range (0x00–0xFF).

---

## Notes

### Driver Examples

```asm
putchar:                     ; send byte in A to terminal
    MOV B, [0xFD]            ; check TX_STATUS
    AND B, 1
    JZ putchar               ; spin (future baud-rate emulation)
    MOV [0xFC], A            ; TX_DATA = byte
    RET

getchar:                     ; blocking read → result in A
    MOV A, [0xFF]            ; check RX_STATUS
    AND A, 1
    JZ getchar               ; spin until data available
    MOV A, [0xFE]            ; read RX_DATA
    MOV [0xFE], 0            ; signal consumed
    RET
```
