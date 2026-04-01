# 3. CPU Architecture

> Architecture v3 | Part of [Technical Specification](spec.md) | See also: [ISA](isa.md), [Memory Model & Addressing](mem.md), [Microarchitecture](uarch.md), [FPU](fp.md), [Vector Unit](vector.md)

## 3.1 Processor States

| State | Description |
|-------|-------------|
| IDLE | Initial state; IP=0, SP=0xE7, DP=0, F=0, Z=0, C=0, regs=0, FA=0, FB=0, FPCR=0, FPSR=0, VA=0, VB=0, VC=0, VM=0, VL=0, VFPSR=0, VU queue empty |
| RUNNING | Executing instructions |
| HALTED | Opcode 0 encountered |
| FAULT | F=1, error code in A; see [Error Codes](errors.md) |

State transitions:

```
IDLE ──step()──► RUNNING ──HLT──► HALTED
                    │                 │
                    ├──error──► FAULT │
                    │             │   │
                    ◄──reset()────┴───┘
```

**Notes:**
- `step()` — execute one instruction; first call transitions IDLE→RUNNING
- When `HLT` is encountered, CPU enters HALTED and `IP` remains pointing at the `HLT` opcode byte.
- `reset()` — signal that returns CPU to IDLE state from HALTED or FAULT
- CPU starts in IDLE after power-on

**Fault invariant:** Every transition into FAULT state is accompanied by a defined error code: CPU sets `F=true` and writes the error code into register `A`.

## 3.2 Instruction Cycle

1. **Fetch:** Read opcode from memory[IP]
2. **Decode:** Determine operation and addressing modes
3. **Validate:** Check operands, stack bounds, division by zero
4. **Execute:** Perform operation, compute [flags](isa.md#16-flag-behavior)
5. **Writeback:** Store result, update IP/SP

**Important:** Validation occurs before any state modification. For example, PUSH faults when `SP == 0` before writing to memory. If validation fails, CPU enters FAULT without modifying memory or registers (except F and A for error code; see [Error Codes](errors.md)).

**FP instruction validation:** FP instructions (opcodes 128-162) additionally validate the FPM byte during the Decode/Validate phase. An invalid FPM byte triggers FAULT(`ERR_FP_FORMAT`) before any FP register or memory modification. FP arithmetic exceptions (Invalid, DivZero, Overflow, Underflow, Inexact) are checked during Execute and always set the corresponding FPSR sticky flag — they never cause FAULT. See [FPU Exception Model](fp.md#77-fp-exception-model).

**Vector instruction handling:** Synchronous vector instructions (VSET, VFSTAT, VFCLR, VWAIT; opcodes 163–169) follow the standard instruction cycle. Asynchronous vector instructions (opcodes 170–183) replace the Execute/Writeback phases with: Validate VFM byte → Resolve addresses from VA/VB/VC/VM/VL → Apply auto-increment → Push resolved command to VU queue (stall if full) → Advance IP. The VU executes commands independently. VWAIT blocks the CPU until the VU queue drains; if the VU encountered a fault, VWAIT transitions CPU to FAULT. See [Vector Unit](vector.md).

**VU queue on reset:** Entering IDLE (reset) or FAULT flushes the VU command queue. All pending VU commands are discarded.

For implementation pseudocode, see [Microarchitecture](uarch.md#41-execution-loop).
