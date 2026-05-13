# 11. Matrix Unit (MU)

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Vector Unit](vu.md)

## 11.1 Overview

Asynchronous coprocessor for matrix multiplication. The CPU snapshots MU state into a FIFO command queue and continues executing; MU runs independently until synchronized with `MWAIT`.

## 11.2 Registers

| Register | Width | Description |
|----------|-------|-------------|
| MA, MB, MC | 16-bit | Address pointers to A / B / C matrices |
| MM, MN, MK | 16-bit | Matrix dimensions: `M` rows of A/C, `N` cols of B/C, `K` inner dim |
| MFPSR | 8-bit | Sticky FP exception flags for FP MMUL / MMAD (same bit layout as VFPSR) |

Codes: `0=MA`, `1=MB`, `2=MC`, `3=MM`, `4=MN`, `5=MK`. Only `MA/MB/MC` are valid MMUL/MMAD pointer operands.

## 11.3 Properties

- Queue: FIFO, in-order, depth 4.
- Memory: shared 64 KB, absolute addressing, DP ignored, no coherence.
- Dimensions: `MM/MN/MK` are unsigned 16-bit.
- Source formats: `.F`, `.H`, `.BF`, `.O3`, `.O2`, `.U`, `.I`.
- Output: C always uses 4-byte elements: FP32 for floating formats, UINT32 for `.U`, INT32 for `.I`.
- Layout default: `.rrr`.
- Auto-increment at enqueue time: `MA += M×K×source_elem_size`, `MB += K×N×source_elem_size`; `MC` is **not** auto-incremented (it stays put so K-loop accumulation does not need to re-MSET it). When the same pointer register is used in multiple operand positions, the increments above are merged so the register advances once by the largest applicable stride.
- `M=0` or `N=0` or `K=0` makes the command a no-op.
- Cost: `ceil(M × N × K / parallelism)` MU ticks; not counted in CPU `cycles`.

## 11.4 Instructions

### 11.4.1 Sync

Sync instructions configure MU state, read status, and synchronize CPU with the MU queue.

| Mnemonic | Description | Encoding |
|----------|-------------|----------|
| `MSET` | Load `MA/MB/MC/MM/MN/MK` from 16-bit immediate | `[188, mreg, imm_lo, imm_hi]` |
| `MSET` | Load `MA/MB/MC/MM/MN/MK` from register pair or zero-extended register | `[189, mreg, (regH<<2)\|regL]` or `[189, mreg, 0x10\|reg]` |
| `MFSTAT` | Copy `MFPSR` to register | `[190, reg]` |
| `MFCLR` | Clear `MFPSR` | `[191]` |
| `MWAIT` | Drain MU queue and surface deferred MU faults | `[192]` |

Here `mreg` is a MU register code: `0=MA`, `1=MB`, `2=MC`, `3=MM`, `4=MN`, `5=MK`.

### 11.4.2 Async Matrix Arithmetic

Async matrix arithmetic consumes the current MU register state, snapshots it into the queue, and computes either `C = A @ B` or `C += A @ B`.

| Mnemonic | Description | Encoding |
|----------|-------------|----------|
| `MMUL` | Matrix multiply: `C = A @ B` | `[193, mfm, mregs]` |
| `MMAD` | Matrix multiply-accumulate: `C += A @ B` | `[194, mfm, mregs]` |

- Format suffix is mandatory.
- Layout suffix is optional and defaults to `.rrr`.
- `fmt` selects A/B source format: `.F`, `.H`, `.BF`, `.O3`, `.O2`, `.U`, `.I`.
- `layout` is `.abc`, where each letter is `r` or `c` for layout of A, B, C.
- `mfm`: bits[2:0] = A/B source format, bits[5:3] = layout mode (`bit5=A_col`, `bit4=B_col`, `bit3=C_col`), bits[7:6] = 0.
- `mregs`: `dst=MC`, `src1=MA`, `src2=MB`, encoded as `(dst<<6) | (src1<<4) | (src2<<2)`; bits[1:0] = 0.

- `MMUL.fmt[.layout] MC, MA, MB` performs:

$$
C[m, n] = \sum_{t=0}^{K-1} A[m, t] \cdot B[t, n]
$$

- `MMAD.fmt[.layout] MC, MA, MB` performs:

$$
C[m, n] = C[m, n] + \sum_{t=0}^{K-1} A[m, t] \cdot B[t, n]
$$

Addressing rules:

- A is logical shape `M × K` at `[MA]`:
  - `.r..`: `(m * K + t) * source_elem_size`
  - `.c..`: `(t * M + m) * source_elem_size`
- B is logical shape `K × N` at `[MB]`:
  - `..r.`: `(t * N + n) * source_elem_size`
  - `..c.`: `(n * K + t) * source_elem_size`
- C is logical shape `M × N` at `[MC]`:
  - `...r`: `(m * N + n) * 4`
  - `...c`: `(n * M + m) * 4`

Numeric rules:

- MMUL seeds the accumulator with zero; MMAD seeds it from stored `C[m,n]`.
- Floating source formats produce FP32 output and accumulate MFPSR flags: NV, OF, UF, NX.
- Integer source formats produce UINT32 (`.U`) or INT32 (`.I`) output and do not modify MFPSR. Integer arithmetic wraps modulo 2³².

### 11.4.3 Pseudo-ops

Pseudo-ops are assembler sugar only; they do not allocate opcodes.

| Mnemonic | Description | Encoding |
|----------|-------------|----------|
| `MSHAPE` | Load shape registers | Expands to `MSET mreg, imm16` × 3 (`MM`, `MN`, `MK`) |

## 11.5 Faults

- MU shares fault codes with VU.
- **ERR_VU_FORMAT** (decode): `mfm` bits[7:6] ≠ 0; format code 7; `mregs` bits[1:0] ≠ 0; any operand register code > 2.
- **ERR_VU_OOB** (deferred via MWAIT): any A/B/C extent extends past 64 KB.
- **ERR_INVALID_REG** (decode): MSET target > 5.

## 11.6 Notes

- `VWAIT` is required before MU reads data produced by VU; `MWAIT` is required before CPU or VU reads data produced by MU.
- Memory is shared and non-coherent while commands are outstanding.
- `MFCLR` is a CPU-side register write and does not drain the queue; flags from in-flight MU commands will still accumulate into `MFPSR` after `MFCLR`. Call `MWAIT` before `MFCLR` to capture all pending flags first.

