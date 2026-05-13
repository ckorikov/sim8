# Display Test Specification

> Architecture v3 | Part of [Technical Specification](../spec.md) | See also: [I/O Display](../io-display.md), [Memory Model](../mem.md), [Memory Tests](tests-mem.md), [UART Tests](tests-io-uart.md)

## Scope

Tests in this file cover the **display cell** (0xE8–0xFB) behaviors:

- Character output via CPU writes
- Read-back from display cells
- Boundary behavior (0xE7 not display, 0xFC is UART not display)
- DP interaction (display active only when DP=0)

---

## Methodology

| Target | Description |
|--------|-------------|
| `display[i]` | Display cell i (0-based, cell 0 = address 0xE8) |
| `mem[addr]` | Memory byte at absolute address |
| `UART_TX` | Bytes emitted via UART TX port |

---

## D.1 Character Output

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| D1 | `MOV [0xE8], 65; HLT` | display[0]='A' | Write to first display cell |
| D2 | `MOV [0xFB], 90; HLT` | display[19]='Z' | Write to last display cell (0xFB = 0xE8+19) |
| D3 | `MOV [0xE8], 65; MOV [0xE9], 66; HLT` | display[0]='A', display[1]='B' | Two consecutive cells |
| D4 | `MOV [0xE8], 0; HLT` | display[0]=0x00 | Null byte — blank display cell |
| D5 | `MOV [0xE8], 32; HLT` | display[0]=' ' | Space character |

---

## D.2 Read-Back

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| D6 | `MOV [0xE8], 65; MOV A, [0xE8]; HLT` | A=65 | Read back from display cell |
| D7 | `MOV A, [0xE8]; HLT` (no prior write) | A=0 | Initial value 0 |

---

## D.3 Boundary

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| D8 | `MOV [0xE7], 42; HLT` | mem[0xE7]=42, no display effect | 0xE7 is data, not display |
| D9 | `MOV [0xFC], 65; HLT` | display unaffected, UART_TX=['A'] | 0xFC is UART TX, not display |

---

## D.4 DP Interaction

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| D10 | `MOV DP, 0; MOV [0xE8], 65; HLT` | display[0]='A' | DP=0 → display active |
| D11 | `MOV DP, 1; MOV [0xE8], 65; HLT` | display unchanged, mem[1×256+0xE8]=65 | DP≠0 → writes data memory, not display |
| D12 | `MOV DP, 1; MOV A, [0xE8]; HLT` | A = mem[1×256+0xE8] | DP≠0 → reads data memory |
