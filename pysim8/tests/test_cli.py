"""Smoke tests for assembler and simulator CLIs."""

import json
from pathlib import Path

from click.testing import CliRunner

from pysim8.asm import assemble
from pysim8.asm.cli import main


def test_cli_default_output(tmp_path: Path, monkeypatch: object) -> None:
    monkeypatch.chdir(tmp_path)  # type: ignore[attr-defined]
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


# ── Simulator headless CLI ────────────────────────────────────────


class TestHeadless:
    def test_headless_basic(self, tmp_path: Path) -> None:
        from pysim8.sim.tui import main as sim_main

        bin_path = tmp_path / "test.bin"
        code = assemble("MOV A, 42\nHLT", arch=2).code
        bin_path.write_bytes(bytes(code))
        runner = CliRunner()
        result = runner.invoke(sim_main, ["--headless", str(bin_path)])
        assert result.exit_code == 0
        assert "HALTED" in result.output

    def test_headless_with_io(self, tmp_path: Path) -> None:
        from pysim8.sim.tui import main as sim_main

        bin_path = tmp_path / "hello.bin"
        code = assemble(
            'MOV A, 72\nMOV [232], A\nHLT', arch=2
        ).code
        bin_path.write_bytes(bytes(code))
        runner = CliRunner()
        result = runner.invoke(sim_main, ["--headless", str(bin_path)])
        assert result.exit_code == 0
        assert "H" in result.output

    def test_headless_fpu_output(self, tmp_path: Path) -> None:
        from pysim8.sim.tui import main as sim_main

        bin_path = tmp_path / "fp.bin"
        code = assemble("FMOV.H FHA, 1.0\nHLT", arch=2).code
        bin_path.write_bytes(bytes(code))
        runner = CliRunner()
        result = runner.invoke(sim_main, ["--headless", str(bin_path)])
        assert result.exit_code == 0
        assert "FA=0x" in result.output
        assert "FPSR=" in result.output

    def test_headless_json(self, tmp_path: Path) -> None:
        from pysim8.sim.tui import main as sim_main

        bin_path = tmp_path / "test.bin"
        code = assemble("MOV A, 42\nHLT", arch=2).code
        bin_path.write_bytes(bytes(code))
        runner = CliRunner()
        result = runner.invoke(sim_main, ["--json", str(bin_path)])
        assert result.exit_code == 0
        data = json.loads(result.output)
        assert data["state"] == "HALTED"
        assert data["regs"]["a"] == 42
        assert data["flags"]["z"] is False
        assert data["fpu"]["fa"] == 0

    def test_headless_json_stdin(self) -> None:
        from pysim8.sim.tui import main as sim_main

        code = bytes(assemble("MOV A, 42\nHLT", arch=2).code)
        runner = CliRunner()
        result = runner.invoke(sim_main, ["--json", "-"], input=code)
        assert result.exit_code == 0
        data = json.loads(result.output)
        assert data["state"] == "HALTED"
        assert data["regs"]["a"] == 42


class TestAsmStdin:
    def test_asm_binary_stdout(self, tmp_path: Path) -> None:
        import subprocess
        src = tmp_path / "test.asm"
        src.write_text("MOV A, 42\nHLT\n")
        result = subprocess.run(
            ["uv", "run", "pysim8-asm", str(src), "--binary"],
            capture_output=True,
        )
        assert result.returncode == 0
        assert list(result.stdout) == [6, 0, 42, 0]

    def test_asm_stdin_binary(self) -> None:
        import subprocess
        result = subprocess.run(
            ["uv", "run", "pysim8-asm", "-", "--binary"],
            input=b"MOV A, 42\nHLT\n",
            capture_output=True,
        )
        assert result.returncode == 0
        assert list(result.stdout) == [6, 0, 42, 0]

    def test_asm_stdin_no_output_flag(self) -> None:
        runner = CliRunner()
        result = runner.invoke(main, ["-"], input="MOV A, 42\nHLT\n")
        assert result.exit_code != 0
