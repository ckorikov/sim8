# Appendix B: Error Codes

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [CPU Architecture](cpu.md), [Microarchitecture](uarch.md), [FPU](fp.md), [Vector Unit](vector.md)

## Fault Invariant

Entering FAULT state is always accompanied by a defined error code:

- CPU sets `F=true`
- CPU writes the error code to register `A`
- CPU enters FAULT state and stops executing

## Error Code Table

| Code | Name | Description | Raised by |
|------|------|-------------|-----------|
| 1 | ERR_DIV_ZERO | Division by zero | DIV, VDIV.I (via VWAIT) |
| 2 | ERR_STACK_OVERFLOW | PUSH/CALL when SP = 0 | PUSH, CALL |
| 3 | ERR_STACK_UNDERFLOW | POP/RET when SP ≥ 231 | POP, RET |
| 4 | ERR_INVALID_REG | Invalid register code in operand | Any instruction with reg operand |
| 5 | ERR_PAGE_BOUNDARY | Address outside 0-255 | Register indirect addressing, instruction fetch, FP multi-byte access |
| 6 | ERR_INVALID_OPCODE | Unassigned opcode executed | Instruction decode |
| 12 | ERR_FP_FORMAT | Invalid FPM byte (bad fmt/pos/phys) | FP instruction decode (always FAULT) |
| 13 | ERR_VU_OOB | Vector memory access outside 0-65535 | VU command execution (detected at VWAIT) |
| 14 | ERR_VU_FORMAT | Invalid VFM byte or unsupported format for instruction | VU instruction decode (always FAULT) |

**Reserved codes:** Error codes 7-11 are reserved for future architecture versions and are not used in v3.

**Note:** The original value of `A` is lost when a fault occurs. Flags `Z` and `C` retain their pre-fault values; only `F` and `A` are modified.

## FP Exception Handling

FP arithmetic exceptions (Invalid, DivZero, Overflow, Underflow, Inexact) do **not** cause FAULT. Instead, they set sticky flags in FPSR and produce IEEE 754 default results. Programs detect exceptions by reading FPSR via `FSTAT`. See [FPU Exception Model](fp.md#77-fp-exception-model) for details.

`ERR_FP_FORMAT` (code 12) is the only FP-related FAULT. It is a decode-time error triggered by invalid FPM byte encoding, not an arithmetic exception.

## VU Exception Handling

VU FP arithmetic exceptions (Invalid, DivZero, Overflow, Underflow, Inexact) do **not** cause FAULT. Instead, they set sticky flags in **VFPSR** (separate from scalar FPSR) and produce IEEE 754 default results. Programs detect exceptions by reading VFPSR via `VFSTAT` after `VWAIT`. See [VU Registers](vector.md#92-registers) for VFPSR details.

`ERR_VU_FORMAT` (code 14) is a decode-time FAULT triggered by invalid VFM byte encoding or unsupported format (e.g., VDOT.I, VSQRT.I). `ERR_VU_OOB` (code 13) is a runtime fault detected during VU execution when a vector access overflows the 16-bit address space. Runtime VU faults are deferred — the CPU discovers them at the next `VWAIT`.
