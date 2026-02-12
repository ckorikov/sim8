# pysim8

Assembler for the sim8 8-bit CPU. Translates assembly source into machine code
per the [specification](../spec/).

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
```

Specify output file

```bash
uv run pysim8-asm program.asm -o custom.bin
```

Print to stdout without writing a file

```bash
uv run pysim8-asm program.asm -S
```

View compiled binary as hex

```bash
xxd program.bin
```

## Tests

```bash
uv run pytest
```

## Project structure

```
src/pysim8/
  isa.py          ISA definitions: opcodes, registers, instruction table
  asm/
    parser.py     Tokenizer and parser (source -> parsed lines)
    codegen.py    Two-pass assembler (parsed lines -> machine code)
    cli.py        CLI entry point (pysim8-asm command)
tests/
  test_asm.py     Assembler unit tests (149 tests)
  test_cli.py     CLI smoke tests
```
