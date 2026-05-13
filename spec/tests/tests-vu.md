# 10. VU Test Specification

> Architecture v3 | Part of [Technical Specification](../spec.md) | See also: [Vector Unit](../vu.md), [ISA](../isa.md), [Assembler](../asm.md), [Error Codes](../errors.md), [CPU Tests](tests-cpu.md), [FP Tests](tests-fp.md)

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

## 10.7 VSQRT / VEXP / VNEG / VABS — Unary

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
| 42a | `; src=[0.0_bf, 1.0_bf, -1.0_bf]` | mem[dst..] ≈ [1.0_bf, e_bf, 1/e_bf] | VEXP.BF (rel err < 5%) |
|    | `VSET VL, 0, 3; VEXP.BF VC, VA; VWAIT; HLT` | | |
| 42b | `; src=[+inf_bf, -inf_bf, NaN_bf]` | mem[dst..] = [+inf_bf, 0.0_bf, NaN] | VEXP edge cases |
|    |  | VFPSR.NV=1 (NaN) | |
| 42c | `VSET VL, 0, 4; VEXP.U VC, VA; VWAIT; HLT` | FAULT(ERR_VU_FORMAT) | VEXP invalid for integer |
|    | | F=1, A=14 | |
| 42d | `VSET VL, 0, 4; VEXP.BF.vs VC, VA, A; VWAIT; HLT` | FAULT(ERR_VU_FORMAT) | VEXP unary — vs mode rejected |
|    | | F=1, A=14 | |

## 10.7a VFMADD — Fused Multiply-Add

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 42e | `; VA=[1,2,3,4]_f, VB=[5,6,7,8]_f, VC₀=[0.5,1,1.5,2]_f` | mem[VC] = [5.5, 13, 22.5, 34]_f | VFMADD.F vv: VC += VA*VB |
|     | `VSET VL, 0, 4; VFMADD.F VC, VA, VB; VWAIT; HLT` | | |
| 42f | `; VA=[1,2,4,8]_o3 (each 0x38..0x60), VC₀=[0,0,0,0]_o3, A=0x40 (=2.0_o3)` | mem[VC] = [2, 4, 8, 16]_o3 | VFMADD.O3 vs: scalar from GPR |
|     | `VSET VL, 0, 4; VFMADD.O3 VC, VA, A; VWAIT; HLT` | | |
| 42g | `VSET VL, 0, 4; VFMADD.U VC, VA, VB; VWAIT; HLT` | FAULT(ERR_VU_FORMAT) | VFMADD invalid for integer |
|     | | F=1, A=14 | |
| 42h | `VSET VL, 0, 4; VFMADD.F.r VC, VA; VWAIT; HLT` | FAULT(ERR_VU_FORMAT) | VFMADD has no reduction mode |
|     | | F=1, A=14 | |
| 42i | `; VC₀=[NaN, 0, +inf, 0]_f` | mem[VC] contains NaN at [0,2] | VFMADD: NaN/inf*0 → invalid |
|     | `VFMADD.F VC, VA, VB; VWAIT; HLT` | VFPSR.NV=1 | |

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

## 10.10 VMOV — Memory Transfer (vv / vs / vi)

`.vs` is universal memory-scalar broadcast: read 1 element of `fmt` from `mem[VU_ptr]`,
write VL copies. Works for all formats. The s2 pointer does NOT advance.

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 48 | `; src=[10,20,30,40]` | mem[dst..dst+3] = [10,20,30,40] | VMOV vv: raw byte copy |
|    | `VSET VL, 0, 4; VMOV.U VC, VA; VWAIT; HLT` | | |
| 49 | `VSET VL, 0, 4; VMOV.U VA, 0xFF; VWAIT; HLT` | mem[VA₀..VA₀+3] = [0xFF]×4 | VMOV vi: broadcast immediate |
| 50a | `; mem[VB₀]=0x42; VMOV.U.vs VC, VB; VWAIT; HLT` | mem[VC₀..VC₀+3] = [0x42]×4 | VMOV vs: byte broadcast from mem |
|     | | VB unchanged, VC += 4 | |
| 50b | `; mem[VB₀..VB₀+1]=0x3F,0xC0 (=1.5_bf); VMOV.BF.vs VC, VB; VWAIT; HLT` | mem[VC₀..VC₀+7] = (1.5_bf)×4 | VMOV vs: bf16 scalar broadcast |
|     | | VB unchanged, VC += 8 | |
| 50c | `MOV A, 0x77; VMOV.U VC, A; HLT` | assembler error | GPR-broadcast removed |
| 50d | `VFILL.U VC, 5; HLT` | assembler error | VFILL mnemonic removed (use VMOV vi) |

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

Tests opcodes 163–187 fault conditions.

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
| 64a | `VSET VL, 0, 4; VCVT.F.F.r VC, VA; VWAIT` | FAULT(ERR_VU_FORMAT) | VCVT r mode invalid |
|     | | F=1, A=14 | |
| 64b | Encode VCVT with dst_vfm fmt=7 (reserved format) | FAULT(ERR_VU_FORMAT) | VCVT dst format=7 |
|     | | F=1, A=14 | |
| 64c | Encode VCVT with src_vfm fmt=7 (reserved format) | FAULT(ERR_VU_FORMAT) | VCVT src format=7 |
|     | | F=1, A=14 | |
| 64d | Encode VCVT with src_vfm bits [7:3] non-zero | FAULT(ERR_VU_FORMAT) | VCVT src_vfm reserved bits |
|     | | F=1, A=14 | |

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
| 78a | `VCVT.H VC, VA` | `VCVT requires two format suffixes` | Missing src format suffix |
| 78b | `VCVT.H.H.r VC, VA` | `VCVT does not support reduction mode` | Explicit r mode |
| 78c | `VCVT.H.F VC, VA, VB, VC` | assembler error | Too many operands |

---

## 10.17 VCVT — Format Conversion

Tests opcode 183. All tests use VWAIT before HLT unless noted.

**Byte notation:** `f32(x)` = float32 x in LE bytes; `f16(x)` = float16 x in LE bytes; `u8(x)` = uint8 byte; `i8(x)` = int8 byte (two's complement).

### 10.17.1 FP → FP (FCVT Analogue)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 79 | `; VA=[f32(1.0), f32(2.0)]` | `mem[VC₀..VC₀+3] = [f16(1.0), f16(2.0)]` | FP32→FP16 vv, exact |
|    | `VSET VL, 0, 2; VCVT.H.F VC, VA; VWAIT; HLT` | VFPSR.NX=0 | |
|    | `a: DB 0x00,0x00,0x80,0x3F, 0x00,0x00,0x00,0x40` | | f32(1.0), f32(2.0) |
|    | `b: DB 0x00,0x3C, 0x00,0x40` | | expected: f16(1.0), f16(2.0) |
| 80 | `; VA=[f32(1.0), f32(0.5)]` | `mem[VC₀..VC₀+3] = [bfloat16(1.0), bfloat16(0.5)]` | FP32→BF16 vv, exact |
|    | `VSET VL, 0, 2; VCVT.BF.F VC, VA; VWAIT; HLT` | VFPSR.NX=0 | bfloat16 is truncated f32 high bytes |
| 81 | `; VA=[f16(1.0), f16(2.0)]` | `mem[VC₀..VC₀+7] = [f32(1.0), f32(2.0)]` | FP16→FP32 widening, exact |
|    | `VSET VL, 0, 2; VCVT.F.H VC, VA; VWAIT; HLT` | VFPSR.NX=0 | widening never inexact |
| 82 | `; VA=[f32(65536.0)]` | `mem[VC₀..VC₀+1] = f16(+inf) = [0x00,0x7C]` | FP32→FP16 narrowing overflow |
|    | `VSET VL, 0, 1; VCVT.H.F VC, VA; VWAIT; HLT` | VFPSR.OF=1, VFPSR.NX=0 | 65536 > f16_max(65504) |
|    | `a: DB 0x00,0x00,0x80,0x47` | | f32(65536.0) |
| 83 | `; VA=[sNaN_h] (f16 signaling NaN)` | `mem[VC₀..VC₀+3]` is qNaN_f | FP16→FP32 sNaN → qNaN, NV |
|    | `VSET VL, 0, 1; VCVT.F.H VC, VA; VWAIT; HLT` | VFPSR.NV=1 | sNaN input sets NV |
| 84 | `; VA=[f32(1.0/3.0)]` | `mem[VC₀..VC₀+1]` = nearest f16 to 1/3 | FP32→FP16 inexact |
|    | `VSET VL, 0, 1; VCVT.H.F VC, VA; VWAIT; HLT` | VFPSR.NX=1 | 1/3 not exactly f16-representable |

### 10.17.2 int → FP (FITOF Analogue)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 85 | `; VA=[u8(1), u8(2), u8(10)]` | `mem[VC₀..VC₀+11] = [f32(1.0), f32(2.0), f32(10.0)]` | UINT8→FP32 exact |
|    | `VSET VL, 0, 3; VCVT.F.U VC, VA; VWAIT; HLT` | VFPSR=0 | all uint8 exact in f32 |
| 86 | `; VA=[u8(0), u8(127), u8(255)]` | `mem[VC₀..] = [f32(0.0), f32(127.0), f32(255.0)]` | UINT8→FP32 boundary values |
|    | `VSET VL, 0, 3; VCVT.F.U VC, VA; VWAIT; HLT` | VFPSR=0 | |
| 87 | `; VA=[i8(-10)=0xF6, i8(0), i8(127)=0x7F]` | `mem[VC₀..] = [f32(-10.0), f32(0.0), f32(127.0)]` | INT8→FP32 signed |
|    | `VSET VL, 0, 3; VCVT.F.I VC, VA; VWAIT; HLT` | VFPSR=0 | |
|    | `a: DB 0xF6, 0x00, 0x7F` | | |
| 88 | `; VA=[i8(-128)=0x80]` | `mem[VC₀..] = f32(-128.0)` | INT8 min → FP32 |
|    | `VSET VL, 0, 1; VCVT.F.I VC, VA; VWAIT; HLT` | VFPSR=0 | exact |
|    | `a: DB 0x80` | | |
| 89 | `; VA=[u8(1), u8(2)]` | `mem[VC₀..VC₀+3] = [f16(1.0), f16(2.0)]` | UINT8→FP16 exact |
|    | `VSET VL, 0, 2; VCVT.H.U VC, VA; VWAIT; HLT` | VFPSR=0 | all uint8 exact in f16 |
| 90 | `; VA=[u8(17)]` | `mem[VC₀]` = nearest O3 to 17 | UINT8→OFP8 may round |
|    | `VSET VL, 0, 1; VCVT.O3.U VC, VA; VWAIT; HLT` | VFPSR.NX=1 | 17 not exactly representable in E4M3 |
|    | `a: DB 17` | | |

### 10.17.3 FP → int (FFTOI Analogue, Saturating)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 91 | `; VA=[f32(1.0), f32(10.0), f32(255.0)]` | `mem[VC₀..VC₀+2] = [u8(1), u8(10), u8(255)]` | FP32→UINT8 exact |
|    | `VSET VL, 0, 3; VCVT.U.F VC, VA; VWAIT; HLT` | VFPSR=0 | |
| 92 | `; VA=[f32(300.0)]` | `mem[VC₀] = u8(255)` | FP32→UINT8 upper saturate |
|    | `VSET VL, 0, 1; VCVT.U.F VC, VA; VWAIT; HLT` | VFPSR.NV=1 | 300 > 255 → clamp + NV |
|    | `a: DB 0x00,0x00,0x96,0x43` | | f32(300.0) |
| 93 | `; VA=[f32(-1.0)]` | `mem[VC₀] = u8(0)` | FP32→UINT8 lower saturate |
|    | `VSET VL, 0, 1; VCVT.U.F VC, VA; VWAIT; HLT` | VFPSR.NV=1 | negative → 0 + NV |
|    | `a: DB 0x00,0x00,0x80,0xBF` | | f32(-1.0) |
| 94 | `; VA=[f32(NaN)] = [0x00,0x00,0xC0,0x7F]` | `mem[VC₀] = u8(0)` | FP32→UINT8 NaN → 0 |
|    | `VSET VL, 0, 1; VCVT.U.F VC, VA; VWAIT; HLT` | VFPSR.NV=1 | NaN → 0 + NV |
| 95 | `; VA=[f32(+inf)]` | `mem[VC₀] = u8(255)` | FP32→UINT8 +inf saturate |
|    | `VSET VL, 0, 1; VCVT.U.F VC, VA; VWAIT; HLT` | VFPSR.NV=1 | |
|    | `a: DB 0x00,0x00,0x80,0x7F` | | f32(+inf) |
| 96 | `; VA=[f32(2.7)]` | `mem[VC₀] = u8(2)` | FP32→UINT8 truncates toward zero |
|    | `VSET VL, 0, 1; VCVT.U.F VC, VA; VWAIT; HLT` | VFPSR.NX=1 | 0.7 discarded → NX |
|    | `a: DB 0xCD,0xCC,0x2C,0x40` | | f32(2.7) |
| 97 | `; VA=[f32(128.0)]` | `mem[VC₀] = i8(127) = 0x7F` | FP32→INT8 upper saturate |
|    | `VSET VL, 0, 1; VCVT.I.F VC, VA; VWAIT; HLT` | VFPSR.NV=1 | 128 > 127 → clamp + NV |
|    | `a: DB 0x00,0x00,0x00,0x43` | | f32(128.0) |
| 98 | `; VA=[f32(-129.0)]` | `mem[VC₀] = i8(-128) = 0x80` | FP32→INT8 lower saturate |
|    | `VSET VL, 0, 1; VCVT.I.F VC, VA; VWAIT; HLT` | VFPSR.NV=1 | -129 < -128 → clamp + NV |
|    | `a: DB 0x00,0x00,0x01,0xC3` | | f32(-129.0) |
| 99 | `; VA=[f32(-2.7)]` | `mem[VC₀] = i8(-2) = 0xFE` | FP32→INT8 truncates toward zero |
|    | `VSET VL, 0, 1; VCVT.I.F VC, VA; VWAIT; HLT` | VFPSR.NX=1 | truncation toward zero, not floor |
|    | `a: DB 0xCD,0xCC,0x2C,0xC0` | | f32(-2.7) |
| 100 | `; VA=[f16(NaN)]` | `mem[VC₀] = i8(0)` | FP16→INT8 NaN → 0 |
|     | `VSET VL, 0, 1; VCVT.I.H VC, VA; VWAIT; HLT` | VFPSR.NV=1 | |

### 10.17.4 Modes: vs and vi

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 101 | `; mem[VB₀..VB₀+3] = f32(42.0)` | `mem[VC₀..VC₀+3] = [f16(42.0)]×2` | VCVT.H.F.vs broadcast |
|     | `VSET VL, 0, 2; VCVT.H.F.vs VC, VB; VWAIT; HLT` | VB unchanged | read 1 f32, convert, broadcast 2× f16 |
| 102 | `; mem[VB₀] = u8(10)` | `mem[VC₀..VC₀+7] = [f32(10.0)]×2` | VCVT.F.U.vs broadcast |
|     | `VSET VL, 0, 2; VCVT.F.U.vs VC, VB; VWAIT; HLT` | VB unchanged, VC += 8 | 1 uint8 in, 2 float32 out |
| 103 | `VSET VL, 0, 4; VCVT.H.U VC, 10; VWAIT; HLT` | `mem[VC₀..VC₀+7] = [f16(10.0)]×4` | VCVT vi: uint8 imm → f16 broadcast |
| 104 | `VSET VL, 0, 3; VCVT.U.F VC, 0; VWAIT; HLT` | `mem[VC₀..VC₀+2] = [0x00]×3` | VCVT vi: f32(0.0) immediate → uint8(0) broadcast |
|     | `; immediate = f32(0.0) = [0,0,0,0]` | | src_elem_size=4 so instruction is 4+4=8 bytes |

### 10.17.5 Auto-Increment with Different Strides

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 105 | `; VA=src (f32 array, 8 bytes), VC=dst (f16 array, 4 bytes)` | VA = VA₀+8, VC = VC₀+4 | FP32→FP16: src +VL×4, dst +VL×2 |
|     | `VSET VL, 0, 2; VCVT.H.F VC, VA; VWAIT; HLT` | | VL=2: VA+8, VC+4 |
| 106 | `; VA=src (u8 array, 4 bytes), VC=dst (f32 array, 16 bytes)` | VA = VA₀+4, VC = VC₀+16 | UINT8→FP32: src +VL×1, dst +VL×4 |
|     | `VSET VL, 0, 4; VCVT.F.U VC, VA; VWAIT; HLT` | | VL=4: VA+4, VC+16 |
| 107 | `; VA points to src (also used as dst)` | VA = VA₀+4 | Same register in dst+src: advance once by max stride |
|     | `VSET VL, 0, 2; VCVT.U.H VA, VA; VWAIT; HLT` | | .H src_elem_size=2, .U dst_elem_size=1, VL=2 |
|     | | | dedup: max(VL×1, VL×2) = 4 |

### 10.17.6 Same Format (Identity)

| # | Source | Verify | Description |
|---|--------|--------|-------------|
| 108 | `; VA=[u8(1),u8(2),u8(3)]` | `mem[VC₀..] = [1, 2, 3]` | VCVT.U.U: identity, same as VMOV |
|     | `VSET VL, 0, 3; VCVT.U.U VC, VA; VWAIT; HLT` | VFPSR=0 | no conversion performed |
| 109 | `; VA=[f32(1.0), f32(2.0)]` | `mem[VC₀..] = f32(1.0), f32(2.0)` | VCVT.F.F: identity for FP |
|     | `VSET VL, 0, 2; VCVT.F.F VC, VA; VWAIT; HLT` | VFPSR=0 | |
