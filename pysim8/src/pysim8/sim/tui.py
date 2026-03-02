"""Rich-based TUI for running programs on the 8-bit CPU simulator."""

from __future__ import annotations

import os
import select
import sys
import threading
import time
from pathlib import Path

import click
from rich import box
from rich.console import Console
from rich.live import Live
from rich.panel import Panel
from rich.table import Table
from rich.text import Text

from pysim8.disasm import disasm_insn

from .cpu import CPU
from .memory import IO_START, PAGE_SIZE
from .registers import CpuState
from .tracing import TraceEvent

__all__ = ["run_tui", "main"]

_IO_SIZE = PAGE_SIZE - IO_START  # 24 bytes

_HAS_TERMIOS = os.name != "nt"
if _HAS_TERMIOS:
    import termios
    import tty

# ── Color scheme ──────────────────────────────────────────────────────

_COLORS: dict[str, str] = {
    "MOV": "cyan",
    "ADD": "green", "SUB": "green", "MUL": "green", "DIV": "green",
    "INC": "green", "DEC": "green", "CMP": "green",
    "AND": "green", "OR": "green", "XOR": "green", "NOT": "green",
    "SHL": "green", "SHR": "green",
    "JMP": "yellow", "JC": "yellow", "JNC": "yellow",
    "JZ": "yellow", "JNZ": "yellow", "JA": "yellow", "JNA": "yellow",
    "CALL": "yellow", "RET": "yellow",
    "PUSH": "magenta", "POP": "magenta",
    "HLT": "dim",
}

_STATE_STYLES: dict[CpuState, str] = {
    CpuState.IDLE: "dim",
    CpuState.RUNNING: "bold green",
    CpuState.HALTED: "bold yellow",
    CpuState.FAULT: "bold red",
}

# ── Formatting helpers ────────────────────────────────────────────────


def _hex(val: int | bool) -> str:
    if isinstance(val, bool):
        return str(int(val))
    return f"{val:02X}"


def _fmt_changes(changes: dict[str, int | bool]) -> str:
    return " ".join(
        f"{k}←{_hex(v)}" for k, v in changes.items() if k != "IP"
    )


def _fmt_trace(event: TraceEvent) -> Text:
    asm = disasm_insn(event.opcode, event.operands)
    changes = _fmt_changes(event.changes)
    mnemonic = asm.split()[0] if asm else ""
    color = _COLORS.get(mnemonic, "white")

    text = Text()
    if event.is_fault:
        text.append(f"  {event.ip:02X}", style="bold red")
        text.append("  ", style="")
        text.append(f"{asm:<20s}", style="bold red")
        if changes:
            text.append("  ", style="")
            text.append(changes, style="red")
        text.append("  FAULT", style="bold red")
    else:
        text.append(f"  {event.ip:02X}", style="dim")
        text.append("  ", style="")
        text.append(f"{asm:<20s}", style=color)
        if changes:
            text.append("  ", style="")
            text.append(changes, style="dim")
    return text


def _make_status(cpu: CPU, filename: str, paused: bool = False) -> Panel:
    r = cpu.regs
    io_raw = cpu.display()

    # State label
    if paused:
        state_text = Text("PAUSED", style="bold blue")
    else:
        state_text = Text(cpu.state.value, style=_STATE_STYLES.get(cpu.state, ""))

    # ── Row 1: regs ┊ pointers ┊ flags ──
    row1 = Text()
    for name, val in [("A", r.a), ("B", r.b), ("C", r.c), ("D", r.d)]:
        row1.append(f" {name} ", style="dim")
        row1.append(f"{val:02X}", style="bold" if val else "dim")
    row1.append("  ┊", style="dim")
    for name, val in [("SP", r.sp), ("DP", r.dp), ("IP", r.ip)]:
        row1.append(f" {name} ", style="dim")
        row1.append(f"{val:02X}", style="bold" if val else "dim")
    row1.append("  ┊", style="dim")
    for name, val in [("Z", r.flags.z), ("C", r.flags.c), ("F", r.flags.f)]:
        row1.append(f" {name}", style="dim")
        row1.append(str(int(val)), style="bold yellow" if val else "dim")
    row1.append("  ┊", style="dim")
    row1.append(" cycles ", style="dim")
    row1.append(str(cpu.cycles), style="bold" if cpu.cycles else "dim")

    # ── Row 2: I/O output ──
    io_padded = io_raw.ljust(_IO_SIZE).replace(" ", "·") if io_raw else "·" * _IO_SIZE
    row2 = Text()
    row2.append(" » ", style="dim")
    for ch in io_padded:
        if ch == "·":
            row2.append(ch, style="dim")
        else:
            row2.append(ch, style="bold cyan")

    # FPU register row (arch=2)
    row_fp: Text | None = None
    if cpu.regs.fpu is not None:
        fpu = cpu.regs.fpu
        row_fp = Text()
        for name, val in [("FA", fpu.fa), ("FB", fpu.fb)]:
            row_fp.append(f" {name} ", style="dim")
            row_fp.append(f"{val:08X}", style="bold" if val else "dim")
        row_fp.append("  ┊", style="dim")
        for name, val in [("FPCR", fpu.fpcr), ("FPSR", fpu.fpsr)]:
            row_fp.append(f" {name} ", style="dim")
            row_fp.append(f"{val:02X}", style="bold" if val else "dim")

    # Stack rows vertically
    tbl = Table.grid()
    tbl.add_column()
    tbl.add_row(row1)
    if row_fp is not None:
        tbl.add_row(row_fp)
    tbl.add_row(row2)

    title = Text.assemble(
        ("sim8 ", "dim"),
        state_text,
        (" ", ""),
        (filename, "dim"),
    )
    subtitle = Text("space run/pause · n step · q quit", style="dim")

    return Panel(
        tbl,
        title=title,
        subtitle=subtitle,
        box=box.ROUNDED,
        border_style="dim",
    )


# ── Keyboard listener ────────────────────────────────────────────────

_PANEL_LINES_BASE = 4   # top border + row1 + row2 + bottom border
_PANEL_LINES_FPU = 5    # + row_fp when arch >= 2


def _key_listener(state: dict[str, bool]) -> None:
    if not _HAS_TERMIOS:
        return

    try:
        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
    except (OSError, termios.error):
        return

    try:
        tty.setcbreak(fd)
        while not state["quit"]:
            ready, _, _ = select.select([fd], [], [], 0.1)
            if not ready:
                continue
            ch = sys.stdin.read(1)
            if ch == " ":
                state["paused"] = not state["paused"]
            elif ch == "n":
                state["step"] = True
            elif ch == "q":
                state["quit"] = True
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)


# ── Main TUI loop ────────────────────────────────────────────────────


def run_tui(
    code: list[int],
    filename: str = "<stdin>",
    speed: int = 25,
    paused: bool = False,
    arch: int = 1,
) -> None:
    """Run a program with scrolling trace log and live status bar.

    Space = run/pause, n = single step, q = quit.
    """
    console = Console()
    cpu = CPU(arch=arch)
    cpu.load(code)

    pending: list[TraceEvent] = []
    cpu.tracer = pending.append

    delay = 1.0 / speed if speed > 0 else 0.0
    state: dict[str, bool] = {"paused": paused, "step": False, "quit": False}

    listener = threading.Thread(target=_key_listener, args=(state,), daemon=True)
    listener.start()

    # Push status panel to the bottom of the terminal from the start.
    panel_lines = _PANEL_LINES_FPU if arch >= 2 else _PANEL_LINES_BASE
    pad = console.height - panel_lines
    if pad > 0:
        console.print("\n" * (pad - 1))

    def refresh() -> None:
        for ev in pending:
            console.print(_fmt_trace(ev))
        pending.clear()
        live.update(_make_status(cpu, filename, paused=state["paused"]))

    with Live(
        _make_status(cpu, filename, paused=paused),
        console=console,
        refresh_per_second=max(speed, 4),
        vertical_overflow="visible",
    ) as live:
        while not state["quit"]:
            # Paused — wait for step or unpause
            if state["paused"] and not state["step"]:
                refresh()
                time.sleep(0.05)
                continue

            # Consume single-step request
            stepped = state["step"]
            state["step"] = False

            if not cpu.step():
                break

            refresh()

            # After a single step, stay paused
            if stepped:
                continue
            if delay:
                time.sleep(delay)

        refresh()

    state["quit"] = True


# ── CLI ───────────────────────────────────────────────────────────────


@click.command()
@click.argument("program", default="-")
@click.option("--speed", "-s", default=25, help="Steps per second (0 = max).")
@click.option("--paused", is_flag=True, help="Start paused (use Space to run).")
@click.option(
    "--arch", type=int, default=2,
    help="Architecture version (1=integer, 2=FPU).",
)
@click.option("--headless", is_flag=True, help="Run without TUI, print final state.")
@click.option("--json", "json_out", is_flag=True, help="Output full state as JSON (implies --headless).")
def main(
    program: str, speed: int, paused: bool, arch: int,
    headless: bool, json_out: bool,
) -> None:
    """Run a .bin binary in the TUI simulator.

    Use '-' as PROGRAM to read binary from stdin (requires --headless).
    """
    if json_out:
        headless = True

    if program == "-":
        if not headless:
            click.echo("Error: stdin requires --headless", err=True)
            raise SystemExit(1)
        code = list(click.get_binary_stream("stdin").read())
    else:
        code = list(Path(program).read_bytes())

    if headless:
        run_headless(code, arch=arch, json_out=json_out)
    else:
        run_tui(
            code,
            filename=Path(program).name,
            speed=speed,
            paused=paused,
            arch=arch,
        )


def run_headless(
    code: list[int], *, arch: int = 2, max_steps: int = 100_000,
    json_out: bool = False,
) -> None:
    """Run program without TUI, print final state and I/O output."""
    import json as _json

    cpu = CPU(arch=arch)
    cpu.load(code)
    cpu.run(max_steps=max_steps)

    if json_out:
        state: dict = {
            "code": code,
            "state": cpu.state.value,
            "steps": cpu.steps,
            "cycles": cpu.cycles,
            "regs": {
                "a": cpu.a, "b": cpu.b, "c": cpu.c, "d": cpu.d,
                "sp": cpu.sp, "dp": cpu.dp, "ip": cpu.ip,
            },
            "flags": {
                "z": cpu.zero, "c": cpu.carry, "f": cpu.fault,
            },
            "display": cpu.display(),
        }
        if cpu.regs.fpu is not None:
            fpu = cpu.regs.fpu
            state["fpu"] = {
                "fa": fpu.fa, "fb": fpu.fb,
                "fpcr": fpu.fpcr, "fpsr": fpu.fpsr,
            }
        click.echo(_json.dumps(state))
        return

    io_text = cpu.display()
    if io_text:
        click.echo(io_text)
    click.echo(f"State: {cpu.state.value}  Cycles: {cpu.cycles}")
    if cpu.regs.fpu:
        fpu = cpu.regs.fpu
        click.echo(
            f"FA=0x{fpu.fa:08X} FB=0x{fpu.fb:08X}"
            f" FPSR=0x{fpu.fpsr:02X}"
        )
