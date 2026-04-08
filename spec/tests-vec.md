# 10. VU Test Specification

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [Vector Unit](vector.md), [ISA](isa.md), [Assembler](asm.md), [Error Codes](errors.md), [Integer Tests](tests.md), [FP Tests](tests-fp.md)

## 10.1 Test Methodology

Each test follows the pattern: **assemble** source code, **execute** until HLT or fault, **verify** CPU and VU state.

All tests that use async commands must include a `VWAIT` before `HLT` unless explicitly testing the hazard window. Tests that expect a deferred fault verify the fault at the `VWAIT` instruction.

**Verification targets:**

| Target | Description |
|--------|-------------|
| `A`, `B`, `C`, `D` | GPR values (0–255) |
| `F` | Fault flag (true/false) |
| `A` (on FAULT) | Error code |
| `VA`, `VB`, `VC`, `VM`, `VL` | VU register values (0–65535) |
| `VFPSR` | VU sticky exception flags |
| `VFPSR.NV` | Invalid operation flag |
| `VFPSR.DZ` | Division by zero flag |
| `VFPSR.OF` | Overflow flag |
| `VFPSR.UF` | Underflow flag |
| `VFPSR.NX` | Inexact flag |
| `mem[addr]` | Memory byte at absolute address |
| `mem[addr..addr+n]` | Memory byte range |

**Data setup pattern:** Use `DB` to initialize memory after `HLT` with forward-referenced labels:

```asm
VSET VA, {src}, src
VSET VC, {dst}, dst
VSET VL, 0, 4
VADD.U VC, VA, 1
VWAIT
HLT
src: DB 10, 20, 30, 40
dst: DB 0, 0, 0, 0
```

---

## 10.2 VSET — Loading VU Registers

Tests opcodes 163–166. VSET must not affect CPU flags (Z, C, F).

### 10.2.1 Immediate (Opcode 163)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 1 | `VSET VL, 64` | VL=64 | Small immediate |
|   | `HLT` | | |
| 2 | `VSET VL, 0xFFFF` | VL=65535 | Maximum immediate (16-bit) |
|   | `HLT` | | |
| 3 | `VSET VA, 0x0100` | VA=0x0100 | 16-bit address |
|   | `HLT` | | |
| 4 | `VSET VL, 1` | VL=1 | Single-element count |
|   | `HLT` | | |
| 5 | `VSET VL, 0` | VL=0 | Zero (all commands become no-ops) |
|   | `VSET VA, 0x0200` | VA=0x0200 | |
|   | `HLT` | | |

### 10.2.2 Composite Immediate (Opcode 163, two operands)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 6 | `VSET VA, 1, 0` | VA=0x0100 | page=1, offset=0 |
|   | `HLT` | | |
| 7 | `VSET VA, 0, 16` | VA=0x0010 | page=0, offset=16 |
|   | `HLT` | | |
| 8 | `VSET VL, 0, 64` | VL=64 | hi=0, lo=64 |
|   | `HLT` | | |
| 9 | `VSET VA, {d}, d` | VA=absolute address of d | Label-based composite |
|   | `HLT` | | |
|   | `d: DB 0` | | |
| 10 | `VSET VA, {d}, [d]` | VA=absolute address of d | `[d]` resolves same as `d` |
|    | `HLT` | | |
|    | `d: DB 0` | | |
| 11 | `VSET VA, [d], [d]` | VA=(offset_of_d << 8) \| offset_of_d | Both brackets resolve to offset |
|    | `HLT` | | |
|    | `d: DB 0` | | |
| 12 | `VSET VL, 0xFF, 0xFF` | VL=65535 | Maximum via composite |
|    | `HLT` | | |

### 10.2.3 GPR Pair (Opcode 164)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 13 | `MOV A, 1` | VA=0x0100 | Runtime GPR values |
|    | `MOV D, 0` | | |
|    | `VSET VA, A, D` | | |
|    | `HLT` | | |
| 14 | `MOV B, 0xFF` | VB=0xFF00 | High byte = B |
|    | `MOV C, 0` | | |
|    | `VSET VB, B, C` | | |
|    | `HLT` | | |
| 15 | `MOV A, 0` | VL=256 | lo=0, hi=1 → 0x0100 |
|    | `MOV B, 1` | | |
|    | `VSET VL, B, A` | VL=0x0100 | |
|    | `HLT` | | |

### 10.2.4 Memory Direct (Opcode 165)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 16 | `VSET VL, [len]` | VL=64 | Read 16-bit LE from memory |
|    | `HLT` | | |
|    | `len: DB 64, 0` | | LE: lo=64, hi=0 → 64 |
| 17 | `VSET VA, [ptr]` | VA=0x0100 | 16-bit address from memory |
|    | `HLT` | | |
|    | `ptr: DB 0, 1` | | LE: lo=0, hi=1 → 0x0100 |
| 18 | `MOV DP, 1` | VA=0x0200 | [addr] uses DP |
|    | `VSET VA, [data]` | | reads from page 1 at offset_of(data) |
|    | `HLT` | | |
|    | `@page 1` | | |
|    | `data: DB 0, 2` | | LE: 0x0200 |

### 10.2.5 Memory Indirect (Opcode 166)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 19 | `MOV A, len` | VL=64 | Read via register indirect |
|    | `VSET VL, [A]` | | |
|    | `HLT` | | |
|    | `len: DB 64, 0` | | |
| 20 | `MOV DP, 1` | VC=0x0300 | [gpr] uses DP |
|    | `MOV B, 0` | | reads from DP × 256 + B |
|    | `VSET VC, [B]` | | |
|    | `HLT` | | |
|    | `@page 1` | | |
|    | `DB 0, 3` | | LE at offset 0: 0x0300 |

### 10.2.6 VSET Does Not Affect CPU Flags

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 21 | `ADD A, A` | Z=true, C=false | Set known flags |
|    | `VSET VL, 100` | Z=true, C=false | VSET must not change Z or C |
|    | `HLT` | | |

---

## 10.3 Auto-Increment

Tests that VU register pointers advance correctly at issue time.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 22 | `VSET VA, {a}, a` | (issue) | src1 |
|    | `VSET VC, {c}, c` | (issue) | dst |
|    | `VSET VL, 0, 4` | | 4 elements |
|    | `VADD.U VC, VA, 1` | VA = VA₀+4, VC = VC₀+4 | +S advance for both |
|    | `VWAIT` | | |
|    | `HLT` | | |
|    | `a: DB 10, 20, 30, 40` | | |
|    | `c: DB 0, 0, 0, 0` | | |
| 23 | `VSET VA, {a}, a` | | src1 = src2 = VA |
|    | `VSET VL, 0, 4` | | |
|    | `VADD.U VA, VA, 1` | VA = VA₀+4 | dedup: advance once |
|    | `VWAIT` | | |
|    | `HLT` | | |
|    | `a: DB 1, 2, 3, 4` | | |
| 24 | `VSET VA, {a}, a` | | |
|    | `VSET VL, 0, 4` | | |
|    | `VADD.U VC, VA` | VA = VA₀+4, VC = VC₀+1 | r-mode: dst +s, src1 +S |
|    | `VWAIT` | | |
|    | `HLT` | | |
|    | `a: DB 1, 2, 3, 4` | | |
| 25 | `VSET VL, 0, 0` | | VL=0: no advance |
|    | `VSET VA, {a}, a` | (save VA₀) | |
|    | `VADD.U VC, VA, 1` | VA = VA₀ | VL=0, no advance |
|    | `VWAIT` | | |
|    | `HLT` | | |
|    | `a: DB 0` | | |

---

## 10.4 VADD / VSUB — Arithmetic

Tests opcodes 170–171.

### 10.4.1 Vector-Vector (vv)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 26 | `; src=[1,2,3,4], src2=[5,6,7,8]` | mem[dst..dst+3] = [6,8,10,12] | VADD.U vv |
|    | `VSET VL, 0, 4` | | |
|    | `VADD.U VC, VA, VB` | | |
|    | `VWAIT; HLT` | | |
| 27 | `; src=[10,20,30], src2=[15,15,15]` | mem[dst..dst+2] = [251,251,251] | VSUB.U underflow wraps |
|    | `VSET VL, 0, 3` | VFPSR.UF=1 | |
|    | `VSUB.U VC, VA, VB` | | |
|    | `VWAIT; HLT` | | |

### 10.4.2 GPR Broadcast (vs)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 28 | `MOV A, 5` | mem[dst..dst+3] = [15,25,35,45] | VADD.U vs |
|    | `; src=[10,20,30,40]` | | |
|    | `VSET VL, 0, 4` | | |
|    | `VADD.U VC, VA, A` | | |
|    | `VWAIT; HLT` | | |

### 10.4.3 Immediate Broadcast (vi)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 29 | `; src=[10,20,30,40]` | mem[dst..dst+3] = [11,21,31,41] | VADD.U vi |
|    | `VSET VL, 0, 4` | | |
|    | `VADD.U VC, VA, 1` | | |
|    | `VWAIT; HLT` | | |

### 10.4.4 Reduction (r)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 30 | `; src=[1,2,3,4]` | mem[dst] = 10 | VADD.U r: 1+2+3+4 |
|    | `VSET VL, 0, 4` | | |
|    | `VADD.U VC, VA` | | |
|    | `VWAIT; HLT` | | |

### 10.4.5 Float Arithmetic

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 31 | `; src=[1.0_h, 2.0_h], src2=[3.0_h, 4.0_h]` | mem[dst..] = [4.0_h, 6.0_h] | VADD.H vv |
|    | `VSET VL, 0, 2` | | |
|    | `VADD.H VC, VA, VB` | | |
|    | `VWAIT; HLT` | | |

---

## 10.5 VMUL / VDIV — Multiply and Divide

### 10.5.1 Integer

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 32 | `; src=[2,3,4,5]` | mem[dst..] = [4,9,16,25] | VMUL.U vv |
|    | `VSET VL, 0, 4; VMUL.U VC, VA, VB; VWAIT; HLT` | | |
| 33 | `; src=[10,20,30], src2=[3,4,6]` | mem[dst..] = [3,5,5] | VDIV.U truncates toward 0 |
|    | `VSET VL, 0, 3; VDIV.U VC, VA, VB; VWAIT; HLT` | | |
| 34 | `; src=[1,2,3], src2=[4,0,6]` | FAULT(ERR_DIV_ZERO) at VWAIT | VDIV.U div-by-zero |
|    | `VSET VL, 0, 3; VDIV.U VC, VA, VB; VWAIT; HLT` | F=1, A=1 | |
| 35 | `; src=[1,2,3], src2=[4,0,6]` | VFPSR.DZ=1 | VDIV.F div-by-zero → +Inf, no FAULT |
|    | `VSET VL, 0, 3; VDIV.F VC, VA, VB; VWAIT; HLT` | F=0 | |

---

## 10.6 VMAX / VMIN

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 36 | `; src=[1,5,3], src2=[4,2,6]` | mem[dst..] = [4,5,6] | VMAX.U vv |
|    | `VSET VL, 0, 3; VMAX.U VC, VA, VB; VWAIT; HLT` | | |
| 37 | `; src=[0x80,0x01] (.I = -128, 1)` | mem[dst..] = [0x01, ...] | VMAX.I: signed, 1 > -128 |
|    | `VSET VL, 0, 2; VMAX.I VC, VA, VB; VWAIT; HLT` | | |
| 38 | `; src=[nan_h, 2.0_h], src2=[1.0_h, nan_h]` | mem[dst..] = [2.0_h, 2.0_h] | VMAX.H: NaN → non-NaN |
|    | `VSET VL, 0, 2; VMAX.H VC, VA, VB; VWAIT; HLT` | VFPSR.NV=1 | |

---

## 10.7 VSQRT / VNEG / VABS — Unary

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 39 | `; src=[4.0_h, 9.0_h]` | mem[dst..] = [2.0_h, 3.0_h] | VSQRT.H |
|    | `VSET VL, 0, 2; VSQRT.H VC, VA; VWAIT; HLT` | | |
| 40 | `; src=[1.0_h, -2.0_h]` | mem[dst..] = [-1.0_h, 2.0_h] | VNEG.H |
|    | `VSET VL, 0, 2; VNEG.H VC, VA; VWAIT; HLT` | | |
| 41 | `; src=[0x80, 0x7F] (.I = -128, 127)` | mem[dst..] = [0x80, 0x7F] | VABS.I: -128 wraps |
|    | `VSET VL, 0, 2; VABS.I VC, VA; VWAIT; HLT` | | |
| 42 | `VSET VL, 0, 4; VSQRT.U VC, VA; VWAIT; HLT` | FAULT(ERR_VU_FORMAT) | VSQRT invalid for integer |
|    | | F=1, A=14 | |

---

## 10.8 VDOT — Dot Product

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 43 | `; VA=[1.0_h,2.0_h,3.0_h], VB=[4.0_h,5.0_h,6.0_h]` | mem[VC] = 32.0_h | 1×4+2×5+3×6=32 |
|    | `VSET VL, 0, 3; VDOT.H VC, VA, VB; VWAIT; HLT` | | |
| 44 | `VSET VL, 0, 4; VDOT.U VC, VA, VB; VWAIT; HLT` | FAULT(ERR_VU_FORMAT) | VDOT invalid for integer |
|    | | F=1, A=14 | |

---

## 10.9 VCMP / VSEL — Masking

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 45 | `; VA=[1,5,3,7], VB=[4,2,6,2]` | mem[VM..] = [0xFF,0x00,0xFF,0x00] | VCMP.U.LT: 1<4, 5≥2, 3<6, 7≥2 |
|    | `VSET VL, 0, 4; VCMP.U.LT VM, VA, VB; VWAIT; HLT` | | |
| 46 | `; dst=[10,20,30,40], alt=[1,2,3,4], mask=[0xFF,0x00,0xFF,0x00]` | mem[VC..] = [10,2,30,4] | VSEL: keep where mask=0xFF |
|    | `VSET VL, 0, 4; VSEL.U VC, VB; VWAIT; HLT` | | |
| 47 | `; VA=[0x80,0x01] (.I)` | mem[VM..] = [0x00,0xFF] | VCMP.I.GT: -128 not > 1 |
|    | `VSET VL, 0, 2; VCMP.I.GT VM, VA, VB; VWAIT; HLT` | | |

---

## 10.10 VMOV / VFILL — Memory Transfer

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 48 | `; src=[10,20,30,40]` | mem[dst..dst+3] = [10,20,30,40] | VMOV: raw byte copy |
|    | `VSET VL, 0, 4; VMOV.U VC, VA; VWAIT; HLT` | | |
| 49 | `VSET VL, 0, 4; VFILL.U VA, 0xFF; VWAIT; HLT` | mem[VA₀..VA₀+3] = [0xFF,0xFF,0xFF,0xFF] | VFILL: fill with constant |
| 50 | `VSET VL, 0, 2; VFILL.F VA, 1.0; VWAIT; HLT` | mem[VA₀..VA₀+7] = float32(1.0) LE × 2 | VFILL.F: 4-byte elements |

---

## 10.11 VFPSR — Exception Flags

Tests that VFPSR accumulates across commands and is cleared by VFCLR.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 51 | `; run VADD.F with overflow input` | VFPSR.OF=1 | Overflow flag set |
|    | `VWAIT; VFSTAT A; HLT` | A has OF bit set | |
| 52 | `; run VADD.F with NaN input` | VFPSR.NV=1 | NV flag accumulates |
|    | `; then run VADD.F with overflow` | VFPSR.NV=1, VFPSR.OF=1 | Both flags sticky |
|    | `VWAIT; VFSTAT A; HLT` | | |
| 53 | `VFCLR` | VFPSR=0 | VFCLR resets all flags |
|    | `VFSTAT A; HLT` | A=0 | |
| 54 | `VFSTAT B` | B=VFPSR | VFSTAT targets any GPR |
|    | `HLT` | F=0 | must not cause FAULT |

---

## 10.12 VWAIT and Async Ordering

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 55 | `VSET VL, 0, 4; VADD.U VC, VA, 1` | mem[VC₀..] updated | CPU continues before VU finishes |
|    | `VWAIT; HLT` | results visible after VWAIT | |
| 56 | `VWAIT; HLT` | no FAULT | VWAIT with empty queue is a no-op |
| 57 | Issue VDIV.U with src2=[0]; `VWAIT` | FAULT(ERR_DIV_ZERO) at VWAIT | Deferred fault surfaces at VWAIT |
|    | | F=1, A=1 | |
| 58 | `VWAIT; VWAIT; HLT` | no FAULT | Two consecutive VWAITs allowed |

---

## 10.13 VL = 0 — No-Op Behavior

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 59 | `VSET VL, 0, 0` | mem[dst] unchanged | VADD with VL=0 is a no-op |
|    | `VADD.U VC, VA, 1; VWAIT; HLT` | VA/VC unchanged | no auto-increment |
| 60 | `VSET VL, 0, 0` | VFPSR=0 | No flags set for no-op |
|    | `VDIV.U VC, VA, VB` | VU never reads memory | |
|    | `VWAIT; HLT` | no FAULT | div-by-zero not triggered |

---

## 10.14 Fault Handling

Tests opcodes 163–183 fault conditions.

### 10.14.1 ERR_VU_FORMAT (code 14) — Decode Time

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 61 | `VSET VL, 0, 4; VDOT.I VC, VA, VB; VWAIT` | FAULT(ERR_VU_FORMAT) | VDOT invalid for integer |
|    | | F=1, A=14 | |
| 62 | `VSET VL, 0, 4; VSQRT.U VC, VA; VWAIT` | FAULT(ERR_VU_FORMAT) | VSQRT invalid for integer |
|    | | F=1, A=14 | |
| 63 | `MOV A, 5` | FAULT(ERR_VU_FORMAT) | GPR broadcast with .F format |
|    | `VSET VL, 0, 4; VADD.F VC, VA, A; VWAIT` | F=1, A=14 | |
| 64 | Invalid VFM byte with cond=7 | FAULT(ERR_VU_FORMAT) | Reserved cond value |
|    | | F=1, A=14 | |

### 10.14.2 ERR_VU_OOB (code 13) — Runtime, Deferred

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 65 | `VSET VA, 0xFF, 0xFE` | FAULT(ERR_VU_OOB) at VWAIT | Last element at 0xFFFF+1 |
|    | `VSET VL, 0, 2` | F=1, A=13 | 2 bytes starting at 0xFFFE: OK, but 2-byte write at 0xFFFF wraps |
|    | `VADD.U VC, VA, 1; VWAIT; HLT` | | |
| 66 | `VSET VA, 0xFF, 0xFC` | FAULT(ERR_VU_OOB) at VWAIT | .H: 4 bytes starting at 0xFFFC |
|    | `VSET VL, 0, 4` | F=1, A=13 | 4 × 2 bytes = 8 bytes, overflows 0xFFFF |
|    | `VADD.H VC, VA, VB; VWAIT; HLT` | | |

---

## 10.15 Bulk / Whole-Memory Operations

Tests that cover maximum VL (65535 elements) operating on the near-full 64 KB address space. These validate correct behavior at VU execution scale limits.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 67 | `VSET VA, 0, 0` | mem[0x0000]=0x01, mem[0x8000]=0x01, mem[0xFFFE]=0x01 | VFILL fills 65535 bytes |
|    | `VSET VL, 0xFF, 0xFF` | | VL=65535 elements, format .U |
|    | `VFILL.U VA, 1` | | |
|    | `VWAIT; HLT` | | |
| 68 | `; memory pre-filled with 1 at 0x0000..0xFFFE` | mem[0x0000]=2, mem[0xFFFE]=2 | VADD.U on 65535 bytes |
|    | `VSET VA, 0, 0` | | |
|    | `VSET VC, 0, 0` | | in-place: src=dst=VA |
|    | `VSET VL, 0xFF, 0xFF` | | |
|    | `VADD.U VC, VA, 1` | | |
|    | `VWAIT; HLT` | | |
| 69 | `VSET VA, 0, 0` | FAULT(ERR_VU_OOB) at VWAIT | VL=65535, .H: 65535×2 = 131070 bytes > 64 KB |
|    | `VSET VL, 0xFF, 0xFF` | F=1, A=13 | |
|    | `VADD.H VC, VA, VB; VWAIT; HLT` | | |
| 70 | `VSET VA, 0, 0` | no FAULT; mem[0] correct | VL=65535, .U: exactly 65535 bytes — fits |
|    | `VSET VC, 0, 0` | | 0x0000 + 65535 = 0xFFFF (last byte) |
|    | `VSET VL, 0xFF, 0xFF` | | |
|    | `VMOV.U VC, VA; VWAIT; HLT` | | |

---

## 10.16 Assembler Validation

Tests that the assembler rejects invalid VU syntax.

| # | Source | Expected error | Description |
|---|--------|----------------|-------------|
| 71 | `VADD VC, VA, VB` | `VU format suffix required` | Missing format suffix |
| 72 | `VADD.X VC, VA, VB` | `Invalid VU format suffix: X` | Unknown suffix |
| 73 | `VCMP.U VM, VA, VB` | `VCMP requires condition suffix` | Missing condition |
| 74 | `VCMP.U.XX VM, VA, VB` | `Invalid VU condition suffix: XX` | Unknown condition |
| 75 | `VDOT.U.vv VC, VA, VB` | `Invalid VU mode for instruction: VDOT` | VDOT vv-only; explicit wrong mode |
| 76 | `VSET VX, 10` | `VSET target must be VA/VB/VC/VM/VL` | Unknown VU register |
| 77 | `VSET VL, 0x10000` | `VSET immediate out of range` | imm16 > 65535 |
| 78 | `VSET VL, 256, 0` | `VSET composite operand out of range` | Composite hi > 255 |
