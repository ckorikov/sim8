# Appendix A: Complete Opcode Table

> Architecture v2 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Instruction Encoding](isa.md#18-instruction-encoding-format), [FPU](fp.md)

| Opcode | Mnemonic | Operands | Bytes |
|--------|----------|----------|-------|
| 0 | HLT | — | 1 |
| 1 | MOV | reg, reg | 3 |
| 2 | MOV | reg, [addr] | 3 |
| 3 | MOV | reg, [reg] | 3 |
| 4 | MOV | [addr], reg | 3 |
| 5 | MOV | [reg], reg | 3 |
| 6 | MOV | reg, const | 3 |
| 7 | MOV | [addr], const | 3 |
| 8 | MOV | [reg], const | 3 |
| 10 | ADD | reg, reg | 3 |
| 11 | ADD | reg, [reg] | 3 |
| 12 | ADD | reg, [addr] | 3 |
| 13 | ADD | reg, const | 3 |
| 14 | SUB | reg, reg | 3 |
| 15 | SUB | reg, [reg] | 3 |
| 16 | SUB | reg, [addr] | 3 |
| 17 | SUB | reg, const | 3 |
| 18 | INC | reg | 2 |
| 19 | DEC | reg | 2 |
| 20 | CMP | reg, reg | 3 |
| 21 | CMP | reg, [reg] | 3 |
| 22 | CMP | reg, [addr] | 3 |
| 23 | CMP | reg, const | 3 |
| 30 | JMP | reg | 2 |
| 31 | JMP | addr | 2 |
| 32 | JC | reg | 2 |
| 33 | JC | addr | 2 |
| 34 | JNC | reg | 2 |
| 35 | JNC | addr | 2 |
| 36 | JZ | reg | 2 |
| 37 | JZ | addr | 2 |
| 38 | JNZ | reg | 2 |
| 39 | JNZ | addr | 2 |
| 40 | JA | reg | 2 |
| 41 | JA | addr | 2 |
| 42 | JNA | reg | 2 |
| 43 | JNA | addr | 2 |
| 50 | PUSH | reg | 2 |
| 51 | PUSH | [reg] | 2 |
| 52 | PUSH | [addr] | 2 |
| 53 | PUSH | const | 2 |
| 54 | POP | reg | 2 |
| 55 | CALL | reg | 2 |
| 56 | CALL | addr | 2 |
| 57 | RET | — | 1 |
| 60 | MUL | reg | 2 |
| 61 | MUL | [reg] | 2 |
| 62 | MUL | [addr] | 2 |
| 63 | MUL | const | 2 |
| 64 | DIV | reg | 2 |
| 65 | DIV | [reg] | 2 |
| 66 | DIV | [addr] | 2 |
| 67 | DIV | const | 2 |
| 70 | AND | reg, reg | 3 |
| 71 | AND | reg, [reg] | 3 |
| 72 | AND | reg, [addr] | 3 |
| 73 | AND | reg, const | 3 |
| 74 | OR | reg, reg | 3 |
| 75 | OR | reg, [reg] | 3 |
| 76 | OR | reg, [addr] | 3 |
| 77 | OR | reg, const | 3 |
| 78 | XOR | reg, reg | 3 |
| 79 | XOR | reg, [reg] | 3 |
| 80 | XOR | reg, [addr] | 3 |
| 81 | XOR | reg, const | 3 |
| 82 | NOT | reg | 2 |
| 90 | SHL | reg, reg | 3 |
| 91 | SHL | reg, [reg] | 3 |
| 92 | SHL | reg, [addr] | 3 |
| 93 | SHL | reg, const | 3 |
| 94 | SHR | reg, reg | 3 |
| 95 | SHR | reg, [reg] | 3 |
| 96 | SHR | reg, [addr] | 3 |
| 97 | SHR | reg, const | 3 |
| | **FP Instructions** | | |
| 128 | FMOV | FP, [addr] | 3 |
| 129 | FMOV | FP, [reg] | 3 |
| 130 | FMOV | [addr], FP | 3 |
| 131 | FMOV | [reg], FP | 3 |
| 132 | FADD | FP, [addr] | 3 |
| 133 | FADD | FP, [reg] | 3 |
| 134 | FSUB | FP, [addr] | 3 |
| 135 | FSUB | FP, [reg] | 3 |
| 136 | FMUL | FP, [addr] | 3 |
| 137 | FMUL | FP, [reg] | 3 |
| 138 | FDIV | FP, [addr] | 3 |
| 139 | FDIV | FP, [reg] | 3 |
| 140 | FCMP | FP, [addr] | 3 |
| 141 | FCMP | FP, [reg] | 3 |
| 142 | FABS | FP | 2 |
| 143 | FNEG | FP | 2 |
| 144 | FSQRT | FP | 2 |
| 145 | FMOV | FP, FP | 3 |
| 146 | FCVT | dst_FP, src_FP | 3 |
| 147 | FITOF | FP, gpr | 3 |
| 148 | FFTOI | gpr, FP | 3 |
| 149 | FSTAT | gpr | 2 |
| 150 | FCFG | gpr | 2 |
| 151 | FSCFG | gpr | 2 |
| 152 | FCLR | — | 1 |
| | **FP Reg-Reg & Extensions** | | |
| 153 | FADD | FP, FP | 3 |
| 154 | FSUB | FP, FP | 3 |
| 155 | FMUL | FP, FP | 3 |
| 156 | FDIV | FP, FP | 3 |
| 157 | FCMP | FP, FP | 3 |
| 158 | FCLASS | gpr, FP | 3 |
| 159 | FMADD | FP, FP, [addr] | 4 |
| 160 | FMADD | FP, FP, [reg] | 4 |
| | **FP Immediate** | | |
| 161 | FMOV | FP, imm8 | 3 |
| 162 | FMOV | FP, imm16 | 4 |

**Total: 109 opcodes** (74 integer + 35 FP)
**Unused (reserved):** 9, 24-29, 44-49, 58-59, 68-69, 83-89, 98-127, 163-255. These ranges are reserved for future architecture versions. Executing a reserved opcode triggers FAULT (`ERR_INVALID_OPCODE`, A=6).
