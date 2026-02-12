# pysim8

Assembler, simulator, and disassembler for the sim8 8-bit CPU.
See [specification](../spec/).

## Requirements

- Python 3.13+
- [uv](https://docs.astral.sh/uv/)

## Install

```bash
uv sync
```

## Assembler

Assemble to binary (default: `source.bin`)

```bash
uv run pysim8-asm program.asm
uv run pysim8-asm program.asm -o custom.bin
uv run pysim8-asm program.asm -S          # print to stdout
```

## Simulator

Run a binary in the TUI (scrolling trace log + register/IO status bar)

```bash
uv run pysim8 program.bin
uv run pysim8 program.bin --speed 50      # steps per second (default: 25, 0 = max)
uv run pysim8 program.bin --paused        # start paused (Space to run)
```

Keys: `Space` run/pause, `n` step, `q` quit.

## Disassembler

Disassemble a binary to readable assembly

```bash
uv run pysim8-disasm program.bin
```

## Tests

```bash
uv run pytest
```

## Project structure

```
src/pysim8/
  isa.py            ISA definitions: opcodes, registers, instruction table
  asm/
    parser.py       Tokenizer and parser (source -> parsed lines)
    codegen.py      Two-pass assembler (parsed lines -> machine code)
    cli.py          CLI entry point (pysim8-asm)
  sim/
    cpu.py          CPU control unit: step/run pipeline
    handlers.py     Instruction handlers (HandlersMixin)
    alu.py          Stateless ALU operations
    memory.py       Memory model (64KB, 256-byte pages)
    registers.py    Register file and flags
    decoder.py      Instruction fetch and decode
    tracing.py      Trace events and callbacks
    tui.py          Rich-based TUI runner (pysim8)
    errors.py       Fault codes
  disasm/
    core.py         Disassembler (machine code -> assembly text)
    cli.py          CLI entry point (pysim8-disasm)
tests/
  test_asm.py       Assembler tests
  test_sim.py       Simulator tests
  test_disasm.py    Disassembler roundtrip tests
  test_cli.py       CLI smoke tests
```
