"""CLI entry point for the assembler."""

from __future__ import annotations

import sys
from pathlib import Path

import click

from pysim8.asm.codegen import assemble, AssemblerError


@click.command()
@click.argument("source", type=click.Path(exists=True))
@click.option("-o", "--output", type=click.Path(), help="Output file (default: SOURCE.bin)")
@click.option("-S", "--stdout", is_flag=True, help="Print to stdout instead of writing file")
def main(source: str, output: str | None, stdout: bool) -> None:
    """Assemble SOURCE file into machine code."""
    text = Path(source).read_text()
    try:
        result = assemble(text)
    except AssemblerError as e:
        click.echo(f"Error: {e}", err=True)
        sys.exit(1)

    code = bytes(result.code)

    if stdout:
        click.echo(f"Assembled {len(code)} bytes")
        click.echo(f"Labels: {result.labels}")
        click.echo(f"Bytes: {list(code)}")
        return

    out_path = Path(output) if output else Path(source).with_suffix(".bin")
    out_path.write_bytes(code)
    click.echo(f"Wrote {len(code)} bytes to {out_path}")
