# sim8

Simulator of an 8-bit computer with CPU and peripherals. Formally verified with TLA+.

[**Web Simulator**](https://ckorikov.github.io/sim8/)

## Structure

```
spec/           Specification
  spec.md         Overview
  isa.md          Instruction set architecture
  isa.json        Opcode table (canonical, machine-readable)
  cpu.md          CPU states and instruction cycle
  mem.md          Memory model and addressing
  uarch.md        Microarchitecture (interpreter pseudocode)
  fp.md           FPU coprocessor (IEEE 754)
  vector.md       Vector Unit (VU) coprocessor
  asm.md          Assembler
  errors.md       Error/fault codes
  tests.md        Test specification (integer)
  tests-fp.md     Test specification (FPU)
  tests-vec.md    Test specification (VU)

formal/         Formal verification
  tla/              TLA+ formal model and tests
    cpu_base.tla      Constants, helpers
    cpu_core.tla      CPU state machine
    cpu_ops_*.tla     Instruction semantics
    tests/            TLC test suites
  z3/               Z3 encoding verification

pysim8/         Python toolchain (assembler, simulator, disassembler)

web/            Browser simulator (vanilla JS, esbuild)

mcp/            MCP server (LLM tool access to assembler, simulator, disassembler)

vscode-sim8/    VS Code extension (syntax highlighting for .asm files)

libs/           Reusable assembly libraries
  std/              Standard I/O routines (print int, string, hex, floats)

examples/       Sample assembly programs
  hello.asm             Hello World (single page)
  hello-mp-code.asm     Hello World, multi-page (code segment)
  hello-mp-data.asm     Hello World, multi-page (data segment)
  quadratic.asm         Quadratic equation solver using FPU

ieee754-test-suite/  IEEE 754 conformance test vectors (.fptest)
```

## Formal Verification

Requires Java and [TLA+ Tools](https://github.com/tlaplus/tlaplus).

Download `tla2tools.jar` into `formal/tla/`:

```bash
cd formal/tla
curl -LO https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
```

Run tests:

```bash
cd formal/tla

make test          # all tests
make test_basic    # single test
make clean         # remove TLC artifacts
```

## pysim8

Python implementation: assembler, TUI simulator, and disassembler. Requires Python 3.13+ and [uv](https://docs.astral.sh/uv/).

```bash
cd pysim8 && uv sync

uv run pysim8-asm program.asm       # assemble → program.bin
uv run pysim8-asm - --binary        # stdin → raw bytes to stdout
uv run pysim8 program.bin           # run in TUI
uv run pysim8 --headless prog.bin   # run without TUI, print state
uv run pysim8 --json prog.bin       # full state as JSON
uv run pysim8-disasm program.bin    # disassemble
uv run pytest                       # tests
```

Unix pipe (assemble + run in one command):

```bash
echo "MOV A, 42\nHLT" | uv run pysim8-asm - --binary | uv run pysim8 --json -
```

See [pysim8/README.md](pysim8/README.md) for details.

## Web Simulator

Browser-based hardware diagram simulator. Vanilla JS, bundled with esbuild, served via GitHub Pages.

```bash
cd web && npm install

npm test           # vitest (unit + integration + cross-validation vs pysim8)
npm run build      # esbuild → dist/sim.bundle.js
```

See [web/](web/) for source structure.

## VS Code Extension

Syntax highlighting for `.asm` files (integer + FP mnemonics, registers, directives, labels, literals).

```bash
code --install-extension vscode-sim8/sim8-asm-0.1.0.vsix
```

See [vscode-sim8/README.md](vscode-sim8/README.md) for the full list of highlighted constructs.

## MCP Server

[Model Context Protocol](https://modelcontextprotocol.io/) server that exposes sim8 tools to LLMs (Claude Desktop, Claude Code, etc.).

Tools: `assemble_source`, `run_program`, `run_binary`, `disassemble`, `get_spec`.

```bash
cd mcp && uv sync

uv run fastmcp dev src/sim8_mcp/server.py:mcp    # debug with Inspector
uv run pytest                                      # tests
```

Add to Claude Code from the repo root:

```bash
claude mcp add sim8 -- uv run --directory ./mcp fastmcp run src/sim8_mcp/server.py:mcp
```

See [mcp/README.md](mcp/README.md) for Claude Desktop config and tool details.

## License

MIT
