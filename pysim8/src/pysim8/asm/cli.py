"""CLI entry point for the assembler."""

from __future__ import annotations

import sys
from pathlib import Path

import click

from pysim8.asm.codegen import assemble, AssemblerError


@click.command()
@click.argument("source", default="-")
@click.option("-o", "--output", type=click.Path(), help="Output file (default: SOURCE.bin)")
@click.option("-S", "--stdout", is_flag=True, help="Print to stdout instead of writing file")
@click.option(
    "--binary", is_flag=True,
    help="Write raw bytes to stdout (for piping into pysim8).",
)
@click.option("--arch", type=click.IntRange(1, 2), default=2, help="Architecture version (1=integer, 2=FPU)")
def main(
    source: str, output: str | None, stdout: bool, binary: bool, arch: int,
) -> None:
    """Assemble SOURCE file into machine code.

    Use '-' as SOURCE to read from stdin.
    """
    if source == "-":
        text = click.get_text_stream("stdin").read()
    else:
        text = Path(source).read_text()

    try:
        result = assemble(text, arch=arch)
    except AssemblerError as e:
        click.echo(f"Error: {e}", err=True)
        sys.exit(1)

    code = bytes(result.code)

    if binary:
        sys.stdout.buffer.write(code)
        return

    if stdout:
        click.echo(f"Assembled {len(code)} bytes")
        click.echo(f"Labels: {result.labels}")
        click.echo(f"Bytes: {list(code)}")
        return

    if source == "-":
        click.echo(f"Error: specify -o, -S, or --binary when reading from stdin", err=True)
        sys.exit(1)

    out_path = Path(output) if output else Path(Path(source).stem + ".bin")
    out_path.write_bytes(code)
    click.echo(f"Wrote {len(code)} bytes to {out_path}")
