# sim8-mcp

MCP server for the 8-bit CPU simulator. Lets LLMs assemble code, run programs, disassemble binaries, and read the CPU specification via [Model Context Protocol](https://modelcontextprotocol.io/).

## Prerequisites

- Python 3.13+
- [uv](https://docs.astral.sh/uv/)

## Install

```bash
cd mcp
uv sync
```

## Run standalone

```bash
cd mcp
uv run fastmcp run src/sim8_mcp/server.py:mcp
```

## Debug with MCP Inspector

```bash
cd mcp
uv run fastmcp dev src/sim8_mcp/server.py:mcp
```

Opens a web UI where you can call each tool interactively.

## Setup with Claude Desktop

Add to your `claude_desktop_config.json` (on macOS: `~/Library/Application Support/Claude/claude_desktop_config.json`):

```json
{
  "mcpServers": {
    "sim8": {
      "command": "uv",
      "args": [
        "run",
        "--directory", "/absolute/path/to/sim8/mcp",
        "fastmcp", "run", "src/sim8_mcp/server.py:mcp"
      ]
    }
  }
}
```

Replace `/absolute/path/to/sim8/mcp` with the actual path to the `mcp/` directory.

Restart Claude Desktop after editing the config. The sim8 tools will appear automatically in new conversations.

## Setup with Claude Code

Run from the repo root:

```bash
claude mcp add sim8 -- uv run --directory ./mcp fastmcp run src/sim8_mcp/server.py:mcp
```

Or add manually to `.mcp.json` in the project root:

```json
{
  "mcpServers": {
    "sim8": {
      "command": "uv",
      "args": [
        "run",
        "--directory", "./mcp",
        "fastmcp", "run", "src/sim8_mcp/server.py:mcp"
      ]
    }
  }
}
```

Verify with `/mcp` in Claude Code to check the server is connected and all 5 tools are listed.

## Tools

### `assemble_source`

Assemble source code into machine code.

- **Input:** `source` — assembly text
- **Output:** `code_hex` (hex string), `labels` (label table), `mapping` (code position -> source line)

### `run_program`

Assemble and run a program to completion (HLT / FAULT / step limit).

- **Input:** `source` — assembly text, `max_steps` (default 100,000)
- **Output:** final CPU state

### `run_binary`

Run a pre-assembled binary.

- **Input:** `code_hex` — hex-encoded machine code, `max_steps` (default 100,000)
- **Output:** final CPU state

### `disassemble`

Disassemble machine code.

- **Input:** `code_hex` — hex string
- **Output:** list of `{"address", "text", "size"}` entries

### `get_spec`

Read a section of the CPU specification.

- **Input:** `section` — one of: `isa`, `opcodes`, `errors`, `cpu`, `mem`, `uarch`, `asm`, `spec`, `tests`
- **Output:** markdown content

## CPU state format

`run_program` and `run_binary` return:

```json
{
  "state": "HALTED",
  "registers": {"A": 42, "B": 0, "C": 0, "D": 0, "SP": 231, "DP": 0, "IP": 5},
  "flags": {"Z": false, "C": false, "F": false},
  "display": ""
}
```

Possible `state` values: `IDLE`, `RUNNING`, `HALTED`, `FAULT`.

When the step limit is reached (state `RUNNING`), a `warning` field is added to the response.

## Tests

```bash
cd mcp
uv run pytest
```
