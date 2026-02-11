# Appendix C: Complete Opcode Table

> Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Instruction Encoding](isa.md#18-instruction-encoding-format)

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

**Total: 74 opcodes**
**Unused ranges:** 9, 24-29, 44-49, 58-59, 68-69, 83-89, 98-255
