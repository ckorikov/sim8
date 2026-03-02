# sim8

Simulator of an 8-bit computer with CPU and peripherals. Formally verified with TLA+.

## Structure

```
spec/           Specification
  spec.md         Overview
  isa.md          Instruction set architecture
  opcodes.md      Opcode table
  cpu.md          CPU states and instruction cycle
  mem.md          Memory model and addressing
  uarch.md        Microarchitecture (interpreter pseudocode)
  asm.md          Assembler
  errors.md       Error/fault codes
  tests.md        Test specification

formal/         TLA+ formal model and tests
  cpu_base.tla      Constants, helpers
  cpu_core.tla      CPU state machine
  cpu_ops_*.tla     Instruction semantics
  tests/            TLC test suites

pysim8/         Python toolchain (assembler, simulator, disassembler)

web/            Browser simulator (vanilla JS, esbuild)

mcp/            MCP server (LLM tool access to assembler, simulator, disassembler)
```

## Formal Verification

Requires Java and [TLA+ Tools](https://github.com/tlaplus/tlaplus).

Download `tla2tools.jar` into `formal/`:

```bash
cd formal
curl -LO https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
```

Run tests:

```bash
cd formal

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
npm run build      # esbuild → docs/sim.bundle.js
```

See [web/](web/) for source structure.

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
