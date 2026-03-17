# sim8 Assembly — VS Code Extension

Syntax highlighting for the [sim8](https://github.com/ckorikov/sim8) 8-bit CPU assembler (v2, with FPU).

## Install

```bash
code --install-extension vscode-sim8/sim8-asm-0.1.0.vsix
```

## What's highlighted

- Integer mnemonics: `MOV`, `ADD`, `JZ`, `CALL`, …
- FP instructions with format suffix: `FADD.H`, `FCVT.F.H`, …
- FP control: `FSTAT`, `FCLR`, …
- Registers: `A`–`D`, `SP`, `DP`, `FA`, `FB`, `FHA`–`FHD`, `FQA`–`FQH`, `FOA`–`FOP`
- Directives: `@page`, `@include`
- `DB` pseudo-instruction
- Labels, strings, character literals
- Number literals: decimal, hex (`0xFF`), binary (`11001000b`), octal (`0o310`)
- Float literals: `1.5`, `3.14_h`, `2.0_bf`, `inf`
- Memory addressing: `[B+3]`, `[0x50]`
- Page expressions: `{label}`
- Comments: `; ...`

## File extensions

`.asm`
