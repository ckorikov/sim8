"""CLI entry point for the assembler."""

from __future__ import annotations

import sys
from pathlib import Path

import click

from pysim8.asm.codegen import AssemblerError, assemble


@click.command()
@click.argument("source", default="-")
@click.option("-o", "--output", type=click.Path(), help="Output file (default: SOURCE.bin)")
@click.option("-S", "--stdout", is_flag=True, help="Print to stdout instead of writing file")
@click.option(
    "--binary",
    is_flag=True,
    help="Write raw bytes to stdout (for piping into pysim8).",
)
@click.option("--arch", type=click.IntRange(1, 3), default=2, help="Architecture version (1=integer, 2=FPU, 3=FPU+VU)")
@click.option(
    "-I", "--include", "include_dirs", multiple=True, type=click.Path(exists=True), help="Add include search path"
)
def main(
    source: str,
    output: str | None,
    stdout: bool,
    binary: bool,
    arch: int,
    include_dirs: tuple[str, ...],
) -> None:
    """Assemble SOURCE file into machine code.

    Use '-' as SOURCE to read from stdin.
    """
    if source == "-":
        text = click.get_text_stream("stdin").read()
        base_path = Path.cwd()
    else:
        src_path = Path(source).resolve()
        text = src_path.read_text()
        base_path = src_path.parent

    inc_paths = [Path(d).resolve() for d in include_dirs] or None

    try:
        result = assemble(text, arch=arch, base_path=base_path, include_paths=inc_paths)
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
        click.echo("Error: specify -o, -S, or --binary when reading from stdin", err=True)
        sys.exit(1)

    out_path = Path(output) if output else Path(Path(source).stem + ".bin")
    out_path.write_bytes(code)
    click.echo(f"Wrote {len(code)} bytes to {out_path}")
