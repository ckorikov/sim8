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

    # ── Row 2: I/O output ──
    io_padded = io_raw.ljust(_IO_SIZE).replace(" ", "·") if io_raw else "·" * _IO_SIZE
    row2 = Text()
    row2.append(" » ", style="dim")
    for ch in io_padded:
        if ch == "·":
            row2.append(ch, style="dim")
        else:
            row2.append(ch, style="bold cyan")

    # Stack rows vertically
    tbl = Table.grid()
    tbl.add_column()
    tbl.add_row(row1)
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

_PANEL_LINES = 4  # top border + row1 + row2 + bottom border


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
) -> None:
    """Run a program with scrolling trace log and live status bar.

    Space = run/pause, n = single step, q = quit.
    """
    console = Console()
    cpu = CPU()
    cpu.load(code)

    pending: list[TraceEvent] = []
    cpu.tracer = pending.append

    delay = 1.0 / speed if speed > 0 else 0.0
    state: dict[str, bool] = {"paused": paused, "step": False, "quit": False}

    listener = threading.Thread(target=_key_listener, args=(state,), daemon=True)
    listener.start()

    # Push status panel to the bottom of the terminal from the start.
    pad = console.height - _PANEL_LINES
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
@click.argument("program", type=click.Path(exists=True))
@click.option("--speed", "-s", default=25, help="Steps per second (0 = max).")
@click.option("--paused", is_flag=True, help="Start paused (use Space to run).")
def main(program: str, speed: int, paused: bool) -> None:
    """Run a .bin binary in the TUI simulator."""
    path = Path(program)
    run_tui(list(path.read_bytes()), filename=path.name, speed=speed, paused=paused)
