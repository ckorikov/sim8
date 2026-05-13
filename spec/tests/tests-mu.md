# 12. MU Test Specification

> Architecture v3 | Part of [Technical Specification](../spec.md) | See also: [Matrix Unit](../mu.md), [ISA](../isa.md), [Assembler](../asm.md), [Error Codes](../errors.md), [CPU Tests](tests-cpu.md), [VU Tests](tests-vu.md)

## 12.1 Test Methodology

Each test follows the pattern: **assemble** source code, **execute** until HLT or fault, **verify** CPU and MU state.

All tests that use async commands must include a `MWAIT` before `HLT` unless explicitly testing the hazard window. Tests that expect a deferred fault verify the fault at the `MWAIT` instruction.

**Verification targets:**

| Target | Description |
|--------|-------------|
| `A`, `B`, `C`, `D` | GPR values (0–255) |
| `F` | Fault flag (true/false) |
| `A` (on FAULT) | Error code |
| `MA`, `MB`, `MC` | MU address pointer values (0–65535) |
| `MM`, `MN`, `MK` | MU dimension register values (0–65535) |
| `MFPSR` | MU sticky FP exception flags |
| `mem[addr]` | Memory byte at absolute address |
| `mem[addr..addr+n]` | Memory byte range |

---

*Tests to be written.*
