"""Smoke test for the assembler CLI."""

from pathlib import Path

from click.testing import CliRunner

from pysim8.asm.cli import main


def test_cli_default_output(tmp_path: Path) -> None:
    src = tmp_path / "test.asm"
    src.write_text("MOV A, 42\nHLT\n")
    runner = CliRunner()
    result = runner.invoke(main, [str(src)])
    assert result.exit_code == 0
    dst = tmp_path / "test.bin"
    assert dst.exists()
    assert list(dst.read_bytes()) == [6, 0, 42, 0]


def test_cli_custom_output(tmp_path: Path) -> None:
    src = tmp_path / "test.asm"
    dst = tmp_path / "custom.bin"
    src.write_text("MOV A, 42\nHLT\n")
    runner = CliRunner()
    result = runner.invoke(main, [str(src), "-o", str(dst)])
    assert result.exit_code == 0
    assert list(dst.read_bytes()) == [6, 0, 42, 0]


def test_cli_stdout(tmp_path: Path) -> None:
    src = tmp_path / "test.asm"
    src.write_text("MOV A, 42\nHLT\n")
    runner = CliRunner()
    result = runner.invoke(main, [str(src), "-S"])
    assert result.exit_code == 0
    assert "4 bytes" in result.output
    assert "Bytes:" in result.output


def test_cli_error(tmp_path: Path) -> None:
    src = tmp_path / "test.asm"
    src.write_text("FOO\n")
    runner = CliRunner()
    result = runner.invoke(main, [str(src)])
    assert result.exit_code != 0
