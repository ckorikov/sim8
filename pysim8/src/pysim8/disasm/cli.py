"""CLI entry point for the disassembler."""

from __future__ import annotations

from pathlib import Path

import click

from pysim8.disasm.core import disasm


@click.command()
@click.argument("binary", type=click.Path(exists=True))
def main(binary: str) -> None:
    """Disassemble a .bin binary file."""
    code = list(Path(binary).read_bytes())

    for addr, text, size in disasm(code):
        hex_bytes = " ".join(f"{code[addr + k]:02X}" for k in range(size))
        click.echo(f"  {addr:04X}:  {hex_bytes:<12s} {text}")
