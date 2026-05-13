# UART Test Specification

> Architecture v3 | Part of [Technical Specification](../spec.md) | See also: [I/O UART](../io-uart.md), [Memory Model](../mem.md), [ISA](../isa.md), [Memory Tests](tests-mem.md), [Display Tests](tests-io-display.md), [CPU Tests](tests-cpu.md)

## Scope

Tests in this file cover the UART terminal port (offsets 0xFC–0xFF on page 0):

- `IO_TX_DATA` (0xFC) — TX byte transmit
- `IO_TX_STATUS` (0xFD) — TX ready flag
- `IO_RX_DATA` (0xFE) — RX byte + consumed signal
- `IO_RX_STATUS` (0xFF) — RX data available flag

Display cell tests (0xE8–0xFB) are in [tests-mem.md](tests-mem.md).
General DP and page-0 memory tests are in [tests-cpu.md §6.21](tests-cpu.md).

---

## Methodology

Each test assembles source, runs to HLT, then verifies simulator-observable I/O state.

| Target | Description |
|--------|-------------|
| `UART_TX` | Bytes emitted to terminal output (in order) |
| `mem[0xFC]` | IO_TX_DATA — cleared to 0 after each emission |
| `mem[0xFD]` | IO_TX_STATUS — bit 0 = TX ready (always 1 in v3) |
| `mem[0xFE]` | IO_RX_DATA — current staged byte (0 if empty) |
| `mem[0xFF]` | IO_RX_STATUS — bit 0 = input available |

---

## U.1 TX — Transmit

### U.1.1 Basic Byte Transmit

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| U1 | `MOV [0xFC], 65; HLT` | UART_TX = ['A'] | Write 'A' (65) to TX_DATA |
| U2 | `MOV [0xFC], 65; MOV [0xFC], 66; HLT` | UART_TX = ['A','B'] | Two consecutive writes |
| U3 | `MOV [0xFC], 0; HLT` | UART_TX = [0x00] | Zero byte transmitted |
| U4 | `MOV [0xFC], 255; HLT` | UART_TX = [0xFF] | Max byte transmitted |

### U.1.2 TX_DATA Cleared After Emission

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| U5 | `MOV [0xFC], 65; HLT` | mem[0xFC] = 0 | TX_DATA cleared to 0 after emit |
| U6 | `MOV [0xFC], 65; MOV A, [0xFC]; HLT` | A=0 | Read after write sees 0 (emitted) |

### U.1.3 TX_STATUS Always Ready

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| U7 | `MOV A, [0xFD]; HLT` | A=1 | TX_STATUS bit 0 = 1 (always ready) |
| U8 | `MOV [0xFC], 65; MOV A, [0xFD]; HLT` | A=1 | Still 1 after transmit |

### U.1.4 Repeated Same Value

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| U9 | `MOV [0xFC], 65; MOV [0xFC], 65; HLT` | UART_TX = ['A','A'] | Each write emits independently |

### U.1.5 TX via putchar Pattern

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| U10 | `putchar: MOV B, [0xFD]; AND B, 1; JZ putchar` | UART_TX = ['H','i'] | Spin on TX_STATUS, then send |
|      | `MOV [0xFC], 'H'; MOV [0xFC], 'i'; HLT` | | TX_STATUS always 1 → no actual spin |

---

## U.2 RX — Receive

### U.2.1 RX Status and Data

| # | Source | Inject input: 'X' | Verify | Description |
|---|---------|-------------------|--------|-------------|
| U11 | `MOV A, [0xFF]; HLT` | 'X' (88) queued | A=1 | RX_STATUS bit 0 = 1 when data available |
| U12 | `MOV A, [0xFF]; HLT` | (no input) | A=0 | RX_STATUS = 0 when empty |
| U13 | `MOV A, [0xFE]; HLT` | 'X' (88) queued | A=88 | RX_DATA = staged byte |
| U14 | `MOV A, [0xFE]; HLT` | (no input) | A=0 | RX_DATA = 0 when empty |

### U.2.2 RX Consume Protocol

| # | Source | Inject: 'A','B' | Verify | Description |
|---|---------|-----------------|--------|-------------|
| U15 | `MOV A, [0xFE]; MOV [0xFE], 0; MOV B, [0xFE]; HLT` | 'A'=65, 'B'=66 | A=65, B=66 | Write 0 → consume → next staged |
| U16 | `MOV A, [0xFE]; HLT` (no consume) | 'A','B' | A=65 | Without write-0, same byte remains |
| U17 | `MOV A, [0xFF]; MOV B, [0xFE]; MOV [0xFE], 0; MOV C, [0xFF]; HLT` | 'A' | A=1, B=65, C=0 | Status clears after consume |

### U.2.3 getchar Pattern

| # | Source | Inject: 'Z' | Verify | Description |
|---|---------|-------------|--------|-------------|
| U18 | `getchar: MOV A, [0xFF]; AND A, 1; JZ getchar` | 'Z' (90) queued | A=90 | Spin on RX_STATUS |
|      | `MOV A, [0xFE]; MOV [0xFE], 0; HLT` | | | Read byte, signal consumed |

---

## U.3 UART + DP Interaction

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| U19 | `MOV DP, 1; MOV A, [0xFC]; HLT` | A = mem[1×256+0xFC] | DP≠0 → [0xFC] is data, not UART |
| U20 | `MOV DP, 0; MOV [0xFC], 65; HLT` | UART_TX = ['A'] | DP=0 → UART port |
| U21 | `MOV DP, 1; MOV [0xFC], 65; HLT` | UART_TX = [] | DP=1 → writes data memory, not UART |

---

## U.4 UART + VU Interaction

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| U22 | VU writes to 0x00FC via VMOV.U | UART_TX unchanged | VU writes to UART port address are memory writes only; UART TX triggers only on CPU write |
