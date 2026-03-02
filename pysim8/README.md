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
uv run pysim8-asm program.asm --binary    # raw bytes to stdout
uv run pysim8-asm - --binary              # read from stdin, raw bytes to stdout
```

## Simulator

Run a binary in the TUI (scrolling trace log + register/IO status bar)

```bash
uv run pysim8 program.bin
uv run pysim8 program.bin --speed 50      # steps per second (default: 25, 0 = max)
uv run pysim8 program.bin --paused        # start paused (Space to run)
uv run pysim8 program.bin --headless      # run without TUI, print final state
uv run pysim8 program.bin --json          # full state as JSON (implies --headless)
uv run pysim8 --json -                    # read binary from stdin
```

Keys: `Space` run/pause, `n` step, `q` quit.

Unix pipe (assemble + run):

```bash
echo "MOV A, 42\nHLT" | uv run pysim8-asm - --binary | uv run pysim8 --json -
```

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
  fp_formats.py     IEEE 754 encode/decode (float32, float16, bfloat16, OFP8)
  asm/
    parser.py       Tokenizer and parser (source -> parsed lines)
    codegen.py      Two-pass assembler (parsed lines -> machine code)
    cli.py          CLI entry point (pysim8-asm)
  sim/
    cpu.py          CPU control unit: step/run pipeline
    handlers.py     Integer instruction handlers (HandlersMixin)
    handlers_fp.py  FPU instruction handlers (HandlersFpMixin)
    alu.py          Stateless ALU operations
    memory.py       Memory model (64KB, 256-byte pages)
    registers.py    Register file, flags, FPU registers
    decoder.py      Instruction fetch and decode
    tracing.py      Trace events and callbacks
    tui.py          Rich-based TUI runner and headless/JSON modes (pysim8)
    errors.py       Fault codes
  disasm/
    core.py         Disassembler (machine code -> assembly text)
    cli.py          CLI entry point (pysim8-disasm)
tests/
  test_asm.py         Assembler tests (integer)
  test_asm_fp.py      Assembler tests (FP instructions)
  test_sim.py         Simulator tests (integer)
  test_sim_fp.py      Simulator tests (FP instructions)
  test_sim_ieee754.py IEEE 754 edge cases (±0, ±∞, NaN, subnormals)
  test_fp8_mldtypes.py OFP8 format tests (E4M3, E5M2)
  test_disasm.py      Disassembler roundtrip tests
  test_cli.py         CLI smoke tests (asm, sim, stdin, --binary, --json)
```
