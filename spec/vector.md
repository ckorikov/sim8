# 9. Vector Unit (VU)

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Error Codes](errors.md), [FPU](fp.md)

## 9.1 Overview

Asynchronous coprocessor for bulk SIMD operations on contiguous memory. The CPU decodes vector instructions, snapshots VU register state into a command, pushes it to a FIFO queue, and continues executing. The VU processes commands independently.

| Property | Value |
|----------|-------|
| Queue | FIFO, in-order (see [uarch §4.6b](uarch.md#46b-vu-pipeline) for depth) |
| Sync instructions | VSET (163–166), VFSTAT (167), VFCLR (168), VWAIT (169) |
| Async commands | VADD–VMOV (170–182) — see `spec/isa.json` |
| Memory | Shared 64 KB, absolute addressing (DP ignored), no coherence |

## 9.2 Registers

All registers are **VU state**, not CPU state.

| Register | Width | Description |
|----------|-------|-------------|
| VA, VB, VC | 16-bit | Address pointers |
| VM | 16-bit | Mask pointer |
| VL | 16-bit | Element count (byte footprint = VL × elem_size) |
| VFPSR | 8-bit | Sticky exception flags (same bit layout as [FPSR](fp.md#74-control-registers)) |

VL = 0 → all commands are no-ops. Exception flags OR-ed across elements per command. Exceptions never cause FAULT (except integer division by zero) — see [Error Codes](errors.md).

**VFPSR flag semantics by format:**

| Bit | Flag | FP formats (F/H/BF/O3/O2) | Integer formats (U/I) |
|-----|------|---------------------------|----------------------|
| 0 | NV | Invalid operation (NaN) | — |
| 1 | DZ | Division by zero → +inf | Division by zero → FAULT |
| 2 | OF | FP overflow | Carry/unsigned overflow (result > 255) |
| 3 | UF | FP underflow | Borrow/unsigned underflow (result < 0) |
| 4 | NX | Inexact (rounding) | — |

Integer overflow/underflow is detected per-element and OR-ed into VFPSR. The result still wraps (mod 256 for U, two's complement for I), but the OF/UF flags record that wrapping occurred.

## 9.3 Data Formats

Codes 0–4: same as scalar [FPM](fp.md#75-fpm-byte-encoding). Plus two VU-only integer formats:

| fmt | Suffix | Format | Size | Notes |
|-----|--------|--------|------|-------|
| 5 | `.U` | UINT8 | 1 B | Unsigned, wrapping mod 256 |
| 6 | `.I` | INT8 | 1 B | Signed two's complement, wrapping |
| 7 | — | Reserved | — | FAULT |

Integer VDIV truncates toward zero. Integer division by zero → FAULT(`ERR_DIV_ZERO`) deferred via VWAIT. VDOT and VSQRT invalid for integer → FAULT.

## 9.4 SIMD Modes

| mode | Semantics ($i = 0 \ldots \text{VL}{-}1$) | Inferred when |
|------|-----------|---------------|
| 0 (vv) | $d[i] = s1[i] \mathbin{op} s2[i]$ | 3rd operand is VU register |
| 1 (vs) | $d[i] = s1[i] \mathbin{op} \text{gpr}$ (GPR scalar broadcast) | 3rd operand is GPR (A–D) |
| 2 (vi) | $d[i] = s1[i] \mathbin{op} \text{imm}$ (immediate broadcast, size = elem_size, LE) | 3rd operand is number |
| 3 (r) | $[d] = s1[0] \mathbin{op} \ldots \mathbin{op} s1[\text{VL}{-}1]$ (reduction, left-to-right) | 2 operands |

**Mode inference:** The assembler infers the mode from operand types. Explicit mode suffixes (`.vv`, `.vs`, `.vi`, `.r`) are accepted for backward compatibility but not required.

**GPR broadcast (mode 1):** The CPU reads the GPR value (8-bit) at issue time and stores it in the command entry. The VU broadcasts this value to all lanes. Restricted to byte formats (O3, O2, U, I); multi-byte FP formats (F, H, BF) → FAULT(`ERR_VU_FORMAT`). Use VMOV vi mode for FP scalar broadcast. The register byte src2 field encodes the GPR code (A=0, B=1, C=2, D=3) when mode=1.

## 9.5 Auto-Increment

At issue time, each pointer advances by the bytes that passed through it.

$S = \text{VL} \times \text{elem\_size}$, $s = \text{elem\_size}$.

| Role | vv | vs | vi | r |
|------|-----|-----|-----|----|
| dst | $+S$ | $+S$ | $+S$ | $+s$ |
| src1 | $+S$ | $+S$ | $+S$ | $+S$ |
| src2 | $+S$ | — | — | — |

**Overrides:** VDOT dst $+s$. VCMP dst $+\text{VL}$. VSEL mask no advance. VMOV unary — dst and src1 only. VMOV vi — dst only.

**Deduplication:** Same register in multiple roles → advance **once** by the largest stride. VL = 0 → no advance.

## 9.6 Async Model

**Issue:** decode → validate VFM → snapshot regs → auto-inc → push (stall if full) → advance IP. Cost: 1 tick. If the queue is full, the CPU stalls until a slot is freed; stall ticks count toward `cycles`.

**Execution:** VU dequeues FIFO, independent of CPU.

**Sync:** VWAIT drains queue. If VU fault occurred → CPU enters FAULT (code in A, F=1).

**Memory hazard window:** From the moment a command is pushed until the next VWAIT, both CPU and VU may access memory concurrently. If both write to the same address, the last writer wins (final value is whichever write lands last — timing-dependent). If one writes and the other reads the same address, the reader may see either the old or new value. Programs must use VWAIT to enforce ordering.

**VFPSR visibility:** VFPSR is updated progressively as the VU processes elements. A VFSTAT executed between two async commands may observe a partial exception state from an in-flight command.

## 9.6a Window Execution Model

The VU reads memory through an **8-byte port**. Each VU tick processes one 8-byte window. The number of elements per tick depends on element size:

| Element size | Formats | Bytes/tick | Elements/tick |
|-------------|---------|-----------|--------------|
| 1 byte | O3, O2, U, I | 8 | 8 |
| 2 bytes | H, BF | 8 | 4 |
| 4 bytes | F | 8 | 2 |

**VU execution cost** = ceil(VL / elements_per_tick) ticks.

The VU processes windows sequentially: each tick consumes the next 8 bytes of data (or fewer for the final partial window). VU ticks run in parallel with CPU ticks at 1:1 rate. Auto-increment pointers (§9.5) are snapshotted at issue time — the window merely indexes into the already-determined memory region.

**Examples:**
- VL=64, format `.U` (1 B) → ceil(64/8) = 8 VU ticks.
- VL=64, format `.F` (4 B) → ceil(64/2) = 32 VU ticks.
- VL=48, format `.H` (2 B) → ceil(48/4) = 12 VU ticks.
- VL=0 → 0 ticks (no-op).

This cost is internal to the VU and does not appear in the CPU `cycles` counter (see [uarch §4.6b](uarch.md#46b-vu-pipeline)).

## 9.7 Instruction Encoding

### VFM Byte (all async commands)

```
  7   6   5   4   3   2   1   0
┌───┬───┬───┬───┬───┬───┬───┬───┐
│  reserved │  mode │    fmt    │
└───┴───┴───┴───┴───┴───┴───┴───┘
```

Bits [7:5] must be 000; non-zero → FAULT(`ERR_VU_FORMAT`).

### VCMP Cond Byte (4th byte, VCMP only)

```
  7   6   5   4   3   2   1   0
┌───┬───┬───┬───┬───┬───┬───┬───┐
│        reserved       │  cond │
└───┴───┴───┴───┴───┴───┴───┴───┘
```

Bits [7:3] must be 0. cond: EQ=0, NE=1, LT=2, LE=3, GT=4, GE=5. Values 6–7 → FAULT(`ERR_VU_FORMAT`).

### Register Byte

```
  7   6   5   4   3   2   1   0
┌───┬───┬───┬───┬───┬───┬───┬───┐
│   dst   │  src1   │  src2   │ 0 │
└───┴───┴───┴───┴───┴───┴───┴───┘
```

2-bit register codes: VA=0, VB=1, VC=2, VM=3. Bits [1:0] reserved (must be 0). Unused fields must be 0.

### Valid Modes per Instruction

| Category | Instructions | Valid modes | Valid formats | Notes |
|----------|-------------|-------------|---------------|-------|
| Arithmetic | VADD–VMIN | vv, vs, vi, r | all | vs: byte formats only (O3/O2/U/I) |
| Dot product | VDOT | vv | FP only | Integer → FAULT(`ERR_VU_FORMAT`) |
| Unary | VSQRT | vv (unary) | FP only | Integer → FAULT(`ERR_VU_FORMAT`) |
| Unary | VNEG, VABS | vv (unary) | all | src2 must be 0 |
| Compare | VCMP | vv | all | 4 bytes (cond in byte 3; see above) |
| Select | VSEL | vv | all | Reads mask from VM |
| Memory | VMOV | vv (unary), vi | all | vi mode: `VFILL` is an assembler alias |

Invalid mode or format combination → FAULT(`ERR_VU_FORMAT`).

## 9.8 Sync Instructions

**VSET** (163–166): Load 16-bit value into VA/VB/VC/VM/VL. Four forms: imm16, gpr-pair, [addr], [reg]. Target codes 0–4.

**VSET gpr-pair encoding (Opcode 164):** The 3rd byte packs two GPR codes as `(rH << 2) | rL`, where rH and rL are 2-bit GPR codes (A=0, B=1, C=2, D=3). The resulting 16-bit value is `(GPR[rH] << 8) | GPR[rL]`. Example: `VSET VL, A, D` encodes the 3rd byte as `(0 << 2) | 3 = 0x03`.

**VFSTAT** (167): Copy VFPSR → GPR. **VFCLR** (168): Clear VFPSR. **VWAIT** (169): Drain queue + surface faults.

## 9.9 Instruction Notes

- **VMAX/VMIN FP:** IEEE 754-2019 — NaN → return non-NaN operand.
- **VMAX/VMIN integer:** `.U` unsigned comparison; `.I` signed comparison (e.g., `VMAX.I` of 0x80 and 0x01 returns 0x01, since −128 < 1).
- **VDOT:** FP only. Intermediate precision ≥ source format.
- **VNEG:** FP flips sign; integer: two's complement negate (wrapping).
- **VABS:** FP clears sign; .U: identity; .I: wrapping (-128 → -128).
- **VCMP:** Byte mask (0xFF/0x00). FP NaN → false (except NE). Integer: `.U` unsigned; `.I` signed. 4-byte encoding (cond in byte 3, see §9.7).
- **VSEL:** `dst[i] = mask[i] ? dst[i] : alt[i]`. Overlap undefined.
- **VMOV:** Unary: raw byte copy, no conversion. vi mode: `dst[i] = imm` broadcast; `VFILL` is an assembler alias. Overlap undefined.

## 9.10 Assembly

```asm
VSET VA, {data}, data          ; {label}=page, label=offset → 16-bit address
VSET VA, 0x0100               ; bare 16-bit immediate
VSET VB, [0x50]               ; read 16-bit from memory
VSET VL, A, D                 ; gpr-pair: (A << 8) | D
VADD.F VC, VA, VB             ; 3 VU regs → vector-vector (mode 0)
VADD.U VC, VA, A              ; GPR → scalar broadcast (mode 1)
VADD.U VC, VA, 42             ; number → immediate broadcast (mode 2)
VADD.U VC, VA                 ; 2 operands → reduction (mode 3)
VDOT.F VC, VA, VB             ; single-mode (always vv)
VCMP.U.LT VM, VA, VB          ; condition suffix (always vv), 4 bytes
VMOV.U VC, VA                 ; unary: raw byte copy
VMOV.U VC, 0                  ; vi mode: broadcast fill (VFILL alias)
VFILL.U VC, 0                 ; same as above
VWAIT                          ; sync
```

Format suffix mandatory. Mode suffix optional — inferred from operands (see §9.4). Condition suffix required for VCMP.
