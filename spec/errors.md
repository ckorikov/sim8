# Error Codes

> Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [CPU Architecture](cpu.md), [Microarchitecture](uarch.md)

## Fault Invariant

Entering FAULT state is always accompanied by a defined error code:

- CPU sets `F=true`
- CPU writes the error code to register `A`
- CPU enters FAULT state and stops executing

## Error Code Table

| Code | Name | Description |
|------|------|-------------|
| 1 | ERR_DIV_ZERO | Division by zero |
| 2 | ERR_STACK_OVERFLOW | PUSH/CALL when SP = 0 |
| 3 | ERR_STACK_UNDERFLOW | POP/RET when SP ≥ 231 |
| 4 | ERR_INVALID_REG | Invalid register code in operand |
| 5 | ERR_PAGE_BOUNDARY | Register indirect offset outside 0–255 |
| 6 | ERR_INVALID_OPCODE | Unassigned opcode executed |

**Note:** The original value of `A` is lost when a fault occurs.
