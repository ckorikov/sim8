# Technical Specification Document

## 8-bit CPU Simulator

**Reference Implementation:** Schweigi/assembler-simulator
**Target Platform:** Modern Web Browsers
**Purpose:** Educational tool for assembly language learning

---

## Table of Contents

| # | Section | File |
|---|---------|------|
| 1 | [Instruction Set Architecture (ISA)](isa.md) | `isa.md` |
| 2 | [Memory Model & Addressing](mem.md) | `mem.md` |
| 3 | [CPU Architecture](cpu.md) | `cpu.md` |
| 4 | [Microarchitecture: Interpreter Model](uarch.md) | `uarch.md` |
| 5 | [Assembler Specification](asm.md) | `asm.md` |
| 6 | [Test Specification](tests.md) | `tests.md` |
| 7 | [Complete Opcode Table](opcodes.md) | `opcodes.md` |
| 8 | [Error Codes](errors.md) | `errors.md` |

---

## Appendix A: Functional Requirements

| Priority | Feature |
|----------|---------|
| High | Code editor, assembler, complete ISA, step/run execution |
| High | CPU state display, memory view, console output |
| Medium | Breakpoints, example programs |
| Low | Export/import source files |

## Appendix B: Reference Resources

- **GitHub:** https://github.com/Schweigi/assembler-simulator
- **Demo:** https://schweigi.github.io/assembler-simulator/
