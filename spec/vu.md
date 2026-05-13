# 9. Vector Unit (VU)

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Error Codes](errors.md), [FPU](fp.md)

## 9.1 Overview

Asynchronous coprocessor for bulk SIMD operations on contiguous memory. The CPU decodes vector instructions, snapshots VU register state into a command, pushes it to a FIFO queue, and continues executing. The VU processes commands independently.

| Property | Value |
|----------|-------|
| Queue | FIFO, in-order (see [uarch §4.6b](uarch.md#46b-vu-pipeline) for depth) |
| Sync instructions | VSET (163–166), VFSTAT (167), VFCLR (168), VWAIT (169) |
| Async commands | VADD–VEXP (170–187), VCVT (183) — see `spec/isa.json` |
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

Integer VDIV truncates toward zero. Integer division by zero → FAULT(`ERR_DIV_ZERO`) deferred via VWAIT. VDOT, VSQRT, VFMADD and VEXP invalid for integer → FAULT.

## 9.4 SIMD Modes

| mode | Semantics ($i = 0 \ldots \text{VL}{-}1$) | Inferred when |
|------|-----------|---------------|
| 0 (vv) | $d[i] = s1[i] \mathbin{op} s2[i]$ | 3rd operand is VU register |
| 1 (vs) | $d[i] = s1[i] \mathbin{op} \text{mem}[s2\_ptr]$ (memory-scalar broadcast — CPU reads 1 element of `fmt` from `mem[s2_ptr]` at issue, snapshots into command, broadcasts) | explicit `.vs` mode suffix; 3rd VU register is the scalar pointer |
| 2 (vi) | $d[i] = s1[i] \mathbin{op} \text{imm}$ (immediate broadcast, size = elem_size, LE) | 3rd operand is number |
| 3 (r) | $[d] = s1[0] \mathbin{op} \ldots \mathbin{op} s1[\text{VL}{-}1]$ (reduction, left-to-right) | 2 operands |

**Mode inference:** The assembler infers the mode from operand types. Explicit mode suffixes (`.vv`, `.vs`, `.vi`, `.r`) are accepted for backward compatibility but not required.

**Memory-scalar broadcast (mode 1, .vs):** The CPU reads `elem_size` bytes from `mem[VU.read_ptr(s2_code)]` at issue time and stores them in the command entry. The VU broadcasts this value to all lanes. Works for **all** formats (FP and integer). The s2 field encodes a VU pointer register (VA=0, VB=1, VC=2, VM=3); the pointer itself does NOT auto-advance — snapshot once, reusable for repeated broadcasts.

## 9.5 Auto-Increment

At issue time, each pointer advances by the bytes that passed through it.

$S = \text{VL} \times \text{elem\_size}$, $s = \text{elem\_size}$.

| Role | vv | vs | vi | r |
|------|-----|-----|-----|----|
| dst | $+S$ | $+S$ | $+S$ | $+s$ |
| src1 | $+S$ | $+S$ | $+S$ | $+S$ |
| src2 | $+S$ | — | — | — |

**Overrides:** VDOT dst $+s$. VCMP dst $+\text{VL}$. VSEL mask no advance. VMOV vv — dst and src1 only. VMOV vs/vi — dst only (s2 pointer in vs does not advance). VGATHER/VSCATTER — see §9.11. VCVT — dst $+\text{VL}\times\text{dst\_elem\_size}$, src1 $+\text{VL}\times\text{src\_elem\_size}$ (strides differ when converting across format boundaries).

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

### VCVT Encoding (Opcode 183, 4 bytes)

```
[183, dst_vfm, src_vfm, reg_byte]
```

- **dst_vfm**: standard VFM byte — bits [7:5] reserved (000), bits [4:3] mode (vv=00, vs=01), bits [2:0] dst_fmt.
- **src_vfm**: format-only VFM byte — bits [7:3] reserved (00000), bits [2:0] src_fmt. (Mode is encoded only in dst_vfm.)
- **reg_byte**: standard register byte. For vs mode, src2 encodes the scalar pointer register; pointer does not auto-advance.

Mode r is invalid for VCVT → FAULT(`ERR_VU_FORMAT`). Reserved bits non-zero → FAULT(`ERR_VU_FORMAT`).

**vi mode:** `[183, dst_vfm, src_vfm, reg_byte, imm×src_elem_size]` — immediate is in src_fmt (src_elem_size bytes, LE), converted to dst_fmt and broadcast to VL elements. Total length: 4 + src_elem_size bytes.

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
| Arithmetic | VADD–VMIN | vv, vs, vi, r | all | vs: explicit `.vs` suffix; s2 (3rd VU reg) is scalar pointer — read 1 element |
| Dot product | VDOT | vv | FP only | Integer → FAULT(`ERR_VU_FORMAT`) |
| Fused MAC | VFMADD | vv, vs, vi | FP only | `dst += src1 * src2`; .vs: s2 is scalar pointer (read 1 elem from mem); integer → FAULT(`ERR_VU_FORMAT`) |
| Unary | VSQRT, VEXP | vv (unary) | FP only | Integer → FAULT(`ERR_VU_FORMAT`) |
| Unary | VNEG, VABS | vv (unary) | all | src2 must be 0 |
| Compare | VCMP | vv | all | 4 bytes (cond in byte 3; see above) |
| Select | VSEL | vv | all | Reads mask from VM |
| Memory | VMOV | vv (unary), vs, vi | all | vv: copy VL elements; .vs: memory-scalar broadcast — s2 (2nd VU reg in syntax) is the scalar pointer; vi: immediate broadcast |
| Gather | VGATHER | vv (unary) | all | Mask compress; see §9.11 |
| Scatter | VSCATTER | vv (unary) | all | Mask expand; see §9.11 |
| Conversion | VCVT | vv, vs, vi | any two formats (including same) | 4-byte base + src_elem_size for vi (see VCVT Encoding above); dst and src elem_size may differ; subsumes FCVT/FITOF/FFTOI scalar analogues |

Invalid mode or format combination → FAULT(`ERR_VU_FORMAT`).

## 9.8 Sync Instructions

**VSET** (163–166): Load 16-bit value into VA/VB/VC/VM/VL. Four forms: imm16, gpr-pair, [addr], [reg]. Target codes 0–4.

**VSET gpr-pair encoding (Opcode 164):** The 3rd byte packs two GPR codes as `(rH << 2) | rL`, where rH and rL are 2-bit GPR codes (A=0, B=1, C=2, D=3). The resulting 16-bit value is `(GPR[rH] << 8) | GPR[rL]`. Example: `VSET VL, A, D` encodes the 3rd byte as `(0 << 2) | 3 = 0x03`.

**VSET single-GPR encoding (Opcode 164):** When bit 4 of the 3rd byte is set, the instruction reads a single GPR (bits 1:0) and zero-extends the 8-bit value to 16-bit. The 3rd byte is `0x10 | gpr_code`. Example: `VSET VL, A` encodes the 3rd byte as `0x10` and sets VL to the value of A (0–255).

**VFSTAT** (167): Copy VFPSR → GPR. **VFCLR** (168): Clear VFPSR. **VWAIT** (169): Drain queue + surface faults.

## 9.9 Instruction Notes

- **VMAX/VMIN FP:** IEEE 754-2019 — NaN → return non-NaN operand.
- **VMAX/VMIN integer:** `.U` unsigned comparison; `.I` signed comparison (e.g., `VMAX.I` of 0x80 and 0x01 returns 0x01, since −128 < 1).
- **VDOT:** FP only. Intermediate precision ≥ source format.
- **VFMADD:** Fused multiply-add `dst[i] = dst[i] + src1[i] × src2[i]`. FP only — integer → FAULT(`ERR_VU_FORMAT`). Modes vv/vs/vi (no reduction). `dst` is read-modify-write; auto-increment treats `dst` as a single output stride (`+S` per call), and accumulation into `dst[i]` happens before the pointer advances. Multiplication uses intermediate precision ≥ source format (same accumulator policy as VDOT). Exception flags accumulate across elements: NV (NaN/sNaN), OF (overflow on `a*b` or final sum), UF (underflow), NX (rounding).
- **VEXP:** Element-wise exp `dst[i] = exp(src1[i])`. FP only — integer → FAULT(`ERR_VU_FORMAT`). vv mode only (unary). exp(±0)=1, exp(+∞)=+∞, exp(−∞)=+0, exp(NaN)=NaN (signaling NaN → NV). Overflow → +∞ + OF + NX; gradual underflow → ±0 + UF + NX. Inexact results set NX.
- **VNEG:** FP flips sign; integer: two's complement negate (wrapping).
- **VABS:** FP clears sign; .U: identity; .I: wrapping (-128 → -128).
- **VCMP:** Byte mask (0xFF/0x00). FP NaN → false (except NE). Integer: `.U` unsigned; `.I` signed. 4-byte encoding (cond in byte 3, see §9.7). See §9.11.
- **VSEL:** `dst[i] = mask[i] ? dst[i] : alt[i]`. Overlap undefined. See §9.11.
- **VMOV:** Unary (vv): raw byte copy, no conversion. vs mode: `dst[i] = mem[s2_ptr]` — CPU reads 1 element of `fmt` from `mem[s2_ptr]` at issue, broadcasts to VL destinations. Works for all formats. vi mode: `dst[i] = imm` broadcast (immediate from instruction stream). vs/vi modes: src1 not used (no auto-increment of src1); s2 pointer in vs does NOT advance (snapshot once). Overlap undefined.
- **VGATHER/VSCATTER:** Mask compress/expand. See §9.11.
- **VCVT:** Element-wise format conversion: `dst[i] = convert<dst_fmt>(src[i])`. Subsumes scalar FCVT/FITOF/FFTOI analogues — the direction is determined by the format suffix pair.
  - **FP → FP:** IEEE 754 rounding. NV if sNaN input. OF (→ ±∞) if narrowing overflows. UF for gradual underflow. NX if result is inexact.
  - **int → FP:** UINT8/INT8 are exactly representable in F/H/BF formats; OFP8 formats (O3/O2) may round — NX only. No NV/OF/UF possible.
  - **FP → UINT8:** Saturate to [0, 255]; truncate toward zero. NaN → 0, NV set. ±∞ or out-of-range → clamp to 0/255, NV set. NX if fractional part discarded.
  - **FP → INT8:** Saturate to [−128, 127]; truncate toward zero. NaN → 0, NV set. Out-of-range → clamp, NV set. NX if fractional part discarded.
  - Same src and dst format: valid identity conversion (equivalent to VMOV.vv, but pointer strides are still computed from the single format).
  - Format 7 in either field → FAULT(`ERR_VU_FORMAT`).

## 9.10 Assembly

```asm
VSET VA, {data}, data          ; {label}=page, label=offset → 16-bit address
VSET VA, 0x0100               ; bare 16-bit immediate
VSET VB, [0x50]               ; read 16-bit from memory
VSET VL, A, D                 ; gpr-pair: (A << 8) | D
VSET VL, A                    ; single GPR: zero-extend A to 16-bit
VADD.F VC, VA, VB             ; 3 VU regs → vector-vector (mode 0)
VADD.U VC, VA, A              ; GPR → scalar broadcast (mode 1)
VADD.U VC, VA, 42             ; number → immediate broadcast (mode 2)
VADD.U VC, VA                 ; 2 operands → reduction (mode 3)
VDOT.F VC, VA, VB             ; single-mode (always vv)
VCMP.U.LT VM, VA, VB          ; condition suffix (always vv), 4 bytes
VMOV.U VC, VA                 ; vv: raw byte copy
VMOV.BF.vs VC, VB             ; vs: read 1 bf16 from mem[VB], broadcast to VL bf16s
VMOV.U VC, 0                  ; vi: broadcast immediate fill
VADD.BF.vs VC, VA, VB         ; arithmetic .vs: VC[i] = VA[i] + mem[VB] (scalar broadcast)
VGATHER.U VB, VA              ; mask compress: pack where VM[i]!=0
VSCATTER.U VB, VA             ; mask expand: unpack where VM[i]!=0
VCVT.H.F VC, VA               ; FP32→FP16 element-wise (FCVT analogue)
VCVT.F.U VC, VA               ; UINT8→FP32 element-wise (FITOF analogue)
VCVT.U.F VC, VA               ; FP32→UINT8 saturating (FFTOI analogue)
VCVT.I.BF VC, VA              ; BF16→INT8 saturating
VCVT.H.F.vs VC, VB            ; convert scalar FP32 at mem[VB] → FP16, broadcast VL times
VCVT.F.U VC, 42               ; vi: convert uint8(42) → float32, broadcast VL times
VWAIT                          ; sync
```

Format suffix mandatory. Mode suffix optional — inferred from operands (see §9.4). Condition suffix required for VCMP.

**VCVT double suffix:** `VCVT.dstfmt.srcfmt` — first suffix is the destination format, second is the source format. Order matches operand order (dst, src). Example: `VCVT.H.F VC, VA` converts VA (float32) → VC (float16).

**Note on VCLASS:** A `VCLASS` instruction (bulk FP classification → UINT8 mask, analogue of scalar FCLASS) is a natural extension but is not included in v3 — no opcode slots remain in the VU range (163–187). Reserved for a future architecture revision.

## 9.11 Mask Operations

The **VM** register points to a byte-mask array in memory. Each byte is either `0x00` (false) or non-zero (true). VCMP produces `0xFF`/`0x00`, but any non-zero value is truthy.

Four instructions use the mask:

| Instruction | VM role | Semantics | VM auto-increment |
|-------------|---------|-----------|-------------------|
| VCMP | write | Compare src1, src2 → write byte mask at [VM] | VM $+\text{VL}$ |
| VSEL | read | `dst[i] = mask[i] ? dst[i] : alt[i]` | no advance |
| VGATHER | read | Compress: pack elements where `mask[i]≠0` | no advance |
| VSCATTER | read | Expand: unpack into positions where `mask[i]≠0` | no advance |

**Mask size:** Always VL bytes (one byte per element), regardless of element format. For `.F` (4 bytes/element), the mask is still VL bytes, not VL×4.

**Typical pattern:**

```asm
; Compare VA > VB, then select
VCMP.U.GT VM, VA, VB        ; mask[i] = (VA[i] > VB[i]) ? 0xFF : 0x00
VSEL.U VC, VA, VB            ; VC[i] = mask[i] ? VC[i] : VA[i]
VWAIT

; Compress: extract every 4th byte (e.g., blue channel from BGRA)
VSET VM, {mask}, mask         ; pre-built [FF,00,00,00] pattern
VGATHER.U VB, VA              ; VB ← packed selected bytes from VA
VWAIT
```

**VGATHER compress:** `j=0; for i in 0..VL-1: if mask[i]: dst[j++] = src[i]`. Output length = popcount of mask. Auto-increment: src $+S$, dst and VM no advance. Overlap undefined.

**VSCATTER expand:** `j=0; for i in 0..VL-1: if mask[i]: dst[i] = src[j++]`. Inverse of VGATHER. Auto-increment: dst $+S$, src and VM no advance. Overlap undefined.

**OOB:** Deterministic pointers are pre-checked on first window. Data-dependent pointers (VGATHER dst, VSCATTER src) are checked per-window at runtime → `ERR_VU_OOB` deferred to VWAIT.
