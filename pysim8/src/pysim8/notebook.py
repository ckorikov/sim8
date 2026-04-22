"""Jupyter notebook integration for pysim8.

Usage::

    from pysim8.notebook import Sim

    sim = Sim(arch=3)
    sim.asm(\"\"\"
        MOV A, 5
        MOV B, 3
        ADD A, B
        HLT
    \"\"\")           # assembles, loads, runs; auto-displays state in Jupyter

    sim.state       # explicit state display (CPU + FPU + VU registers)
    sim.page(0)     # hex dump of memory page 0
    sim.trace       # execution trace
"""

from __future__ import annotations

import base64
import struct
import zlib

from pysim8.asm import assemble
from pysim8.constants import MEM_SIZE, PAGE_SIZE
from pysim8.sim.cpu import CPU
from pysim8.sim.memory import Memory
from pysim8.sim.registers import CpuState, FpuRegisters, RegisterFile
from pysim8.sim.tracing import TraceEvent
from pysim8.sim.vu import VuRegisters

__all__ = ["Sim", "SimState", "MemPage", "MemSlice", "TraceView", "SimDisplay", "MemPad"]

_MEM_COLS = 16  # columns per row in hex dump (PAGE_SIZE = _MEM_COLS²)

_CSS = "font-family:monospace;font-size:13px;border-collapse:collapse"
_TH = "style='padding:3px 8px;background:#e8e8e8;border:1px solid #ccc;text-align:left'"
_TD = "style='padding:3px 8px;border:1px solid #ddd'"
_TD_DIM = "style='padding:3px 8px;border:1px solid #ddd;color:#888'"
_H3 = "style='margin:8px 0 4px;font-family:monospace;font-size:13px;color:#444'"

_PRINTABLE_LOW = 0x20
_PRINTABLE_HIGH = 0x7E


# ── helpers ───────────────────────────────────────────────────────────────────


def _row(*cells: str, header: bool = False) -> str:
    tag = "th" if header else "td"
    style = _TH if header else _TD
    inner = "".join(f"<{tag} {style}>{c}</{tag}>" for c in cells)
    return f"<tr>{inner}</tr>"


def _flag_badge(label: str, active: bool) -> str:
    color = "#2563eb" if active else "#d1d5db"
    text_color = "white" if active else "#6b7280"
    return (
        f"<span style='background:{color};color:{text_color};"
        f"border-radius:3px;padding:1px 5px;margin-right:3px;"
        f"font-size:11px'>{label}</span>"
    )


def _is_printable(b: int) -> bool:
    return _PRINTABLE_LOW <= b <= _PRINTABLE_HIGH


# ── MemPage ───────────────────────────────────────────────────────────────────


class MemPage:
    """256-byte memory page with HTML display.

    Obtained via ``sim.page(n)``.
    """

    def __init__(self, mem: Memory, page: int) -> None:
        self._mem = mem
        self._page = page

    def _iter_rows(self) -> list[tuple[int, list[int]]]:
        """Return list of (base_addr, [bytes]) for each row."""
        base = self._page * PAGE_SIZE
        return [
            (base + row * _MEM_COLS, [self._mem[base + row * _MEM_COLS + col] for col in range(_MEM_COLS)])
            for row in range(PAGE_SIZE // _MEM_COLS)
        ]

    def to_html(self) -> str:
        """Render as an HTML hex dump table."""
        base = self._page * PAGE_SIZE
        lines = [
            f"<h3 {_H3}>Memory page {self._page} (0x{base:04X}–0x{base + PAGE_SIZE - 1:04X})</h3>",
            f"<table style='{_CSS}'><thead><tr>",
            f"<th {_TH}>Addr</th>",
        ]
        for i in range(_MEM_COLS):
            lines.append(f"<th {_TH}>+{i:X}</th>")
        lines.append(f"<th {_TH}>ASCII</th></tr></thead><tbody>")

        for addr, row_bytes in self._iter_rows():
            lines.append(f"<tr><td {_TD_DIM}>{addr:04X}</td>")
            for b in row_bytes:
                style = _TD if b else _TD_DIM
                lines.append(f"<td {style}>{b:02X}</td>")
            ascii_str = "".join(chr(b) if _is_printable(b) else "·" for b in row_bytes)
            lines.append(f"<td {_TD_DIM}>{ascii_str}</td></tr>")

        lines.append("</tbody></table>")
        return "".join(lines)

    def _repr_html_(self) -> str:
        return self.to_html()

    def __repr__(self) -> str:
        base = self._page * PAGE_SIZE
        lines = [f"Page {self._page}  (0x{base:04X}–0x{base + PAGE_SIZE - 1:04X})"]
        for addr, row_bytes in self._iter_rows():
            hex_part = " ".join(f"{b:02X}" for b in row_bytes)
            asc_part = "".join(chr(b) if _is_printable(b) else "." for b in row_bytes)
            lines.append(f"  {addr:04X}  {hex_part}  {asc_part}")
        return "\n".join(lines)


# ── MemSlice ─────────────────────────────────────────────────────────────────


class MemSlice:
    """Arbitrary memory range with HTML display.

    Obtained via ``sim.mem(addr, n)``.
    """

    def __init__(self, mem: Memory, addr: int, n: int) -> None:
        self._mem = mem
        self._addr = addr & 0xFFFF
        self._n = max(1, n)

    def _iter_rows(self) -> list[tuple[int, list[int | None]]]:
        """Return (row_addr, [byte_or_None, ...]) for each row."""
        rows = []
        for offset in range(0, self._n, _MEM_COLS):
            row_addr = (self._addr + offset) & 0xFFFF
            row: list[int | None] = []
            for col in range(_MEM_COLS):
                pos = offset + col
                row.append(self._mem[row_addr + col] if pos < self._n else None)
            rows.append((row_addr, row))
        return rows

    def to_html(self) -> str:
        """Render as an HTML hex dump table."""
        end = (self._addr + self._n - 1) & 0xFFFF
        lines = [
            f"<h3 {_H3}>Memory 0x{self._addr:04X}–0x{end:04X} ({self._n} bytes)</h3>",
            f"<table style='{_CSS}'><thead><tr>",
            f"<th {_TH}>Addr</th>",
        ]
        for i in range(_MEM_COLS):
            lines.append(f"<th {_TH}>+{i:X}</th>")
        lines.append(f"<th {_TH}>ASCII</th></tr></thead><tbody>")

        for row_addr, row_bytes in self._iter_rows():
            lines.append(f"<tr><td {_TD_DIM}>{row_addr:04X}</td>")
            ascii_chars: list[str] = []
            for b in row_bytes:
                if b is None:
                    lines.append(f"<td {_TD_DIM}>  </td>")
                    ascii_chars.append(" ")
                else:
                    style = _TD if b else _TD_DIM
                    lines.append(f"<td {style}>{b:02X}</td>")
                    ascii_chars.append(chr(b) if _is_printable(b) else "·")
            lines.append(f"<td {_TD_DIM}>{''.join(ascii_chars)}</td></tr>")

        lines.append("</tbody></table>")
        return "".join(lines)

    def _repr_html_(self) -> str:
        return self.to_html()

    def __repr__(self) -> str:
        end = (self._addr + self._n - 1) & 0xFFFF
        lines = [f"Memory 0x{self._addr:04X}–0x{end:04X} ({self._n} bytes)"]
        for row_addr, row_bytes in self._iter_rows():
            hex_part = " ".join(f"{b:02X}" if b is not None else "  " for b in row_bytes)
            asc_part = "".join((chr(b) if _is_printable(b) else ".") if b is not None else " " for b in row_bytes)
            lines.append(f"  {row_addr:04X}  {hex_part}  {asc_part}")
        return "\n".join(lines)


# ── TraceView ─────────────────────────────────────────────────────────────────


class TraceView:
    """Execution trace with HTML display.

    Obtained via ``sim.trace``.
    """

    def __init__(self, events: list[TraceEvent]) -> None:
        self._events = events

    def to_html(self) -> str:
        """Render as an HTML table."""
        if not self._events:
            return "<p style='font-family:monospace;color:#888'>No trace events.</p>"

        lines = [
            f"<h3 {_H3}>Trace ({len(self._events)} steps)</h3>",
            f"<table style='{_CSS}'><thead>",
            _row("#", "IP", "Opcode", "Operands", "Changes", "Cost", "Fault", header=True),
            "</thead><tbody>",
        ]
        for i, ev in enumerate(self._events):
            operands = " ".join(f"0x{o:02X}" for o in ev.operands) if ev.operands else "—"
            changes = ", ".join(f"{k}={v}" for k, v in ev.changes.items()) if ev.changes else "—"
            fault_cell = "<span style='color:red'>FAULT</span>" if ev.is_fault else ""
            row_style = " style='background:#fff0f0'" if ev.is_fault else ""
            lines.append(
                f"<tr{row_style}>"
                f"<td {_TD_DIM}>{i}</td>"
                f"<td {_TD}>{ev.ip}</td>"
                f"<td {_TD}>{ev.opcode}</td>"
                f"<td {_TD}>{operands}</td>"
                f"<td {_TD}>{changes}</td>"
                f"<td {_TD_DIM}>{ev.cost if ev.cost else '—'}</td>"
                f"<td {_TD}>{fault_cell}</td>"
                "</tr>"
            )
        lines.append("</tbody></table>")
        return "".join(lines)

    def _repr_html_(self) -> str:
        return self.to_html()

    def __repr__(self) -> str:
        if not self._events:
            return "Trace: (empty)"
        lines = [f"Trace ({len(self._events)} steps):"]
        for i, ev in enumerate(self._events):
            parts = [f"  {i:4d}  IP={ev.ip:3d}  op={ev.opcode:3d}"]
            if ev.operands:
                parts.append(f"operands={list(ev.operands)}")
            if ev.changes:
                parts.append(f"changes={ev.changes}")
            if ev.cost:
                parts.append(f"cost={ev.cost}")
            if ev.is_fault:
                parts.append("FAULT")
            lines.append(" ".join(parts))
        return "\n".join(lines)

    def __len__(self) -> int:
        return len(self._events)

    def __getitem__(self, key: int | slice) -> "TraceEvent | list[TraceEvent]":
        return self._events[key]


# ── SimState ──────────────────────────────────────────────────────────────────


class SimState:
    """Snapshot of CPU state with HTML display.

    Obtained via ``sim.state`` or returned by ``sim.asm()`` / ``sim.run()``.
    """

    def __init__(self, cpu: CPU) -> None:
        self._cpu = cpu

    def to_html(self) -> str:
        """Render as an HTML register table."""
        cpu = self._cpu
        regs: RegisterFile = cpu.regs
        state_color = {
            CpuState.HALTED: "#16a34a",
            CpuState.FAULT: "#dc2626",
            CpuState.RUNNING: "#2563eb",
            CpuState.IDLE: "#6b7280",
        }[cpu.state]

        lines = [
            "<div style='font-family:monospace;font-size:13px'>",
            f"<p style='margin:0 0 6px'>"
            f"<strong style='color:{state_color}'>{cpu.state.value}</strong>"
            f" &nbsp;·&nbsp; {cpu.steps} steps &nbsp;·&nbsp; {cpu.cycles} cycles"
            f"</p>",
        ]

        lines.append(f"<h3 {_H3}>CPU Registers</h3>")
        lines.append(f"<table style='{_CSS}'><tbody>")
        lines.append(_row("A", "B", "C", "D", "SP", "DP", "IP", header=True))
        lines.append(
            _row(
                f"0x{regs.a:02X}",
                f"0x{regs.b:02X}",
                f"0x{regs.c:02X}",
                f"0x{regs.d:02X}",
                f"0x{regs.sp:02X}",
                f"0x{regs.dp:02X}",
                f"0x{regs.ip:02X}",
            )
        )
        lines.append("</tbody></table>")

        flags = regs.flags
        lines.append(
            "<p style='margin:4px 0'>"
            + _flag_badge("Z", flags.z)
            + _flag_badge("C", flags.c)
            + _flag_badge("F", flags.f)
            + "</p>"
        )

        fpu: FpuRegisters | None = regs.fpu
        if fpu is not None:
            lines.append(f"<h3 {_H3}>FPU Registers</h3>")
            lines.append(f"<table style='{_CSS}'><tbody>")
            lines.append(_row("FA", "FB", "FPCR", "FPSR", header=True))
            lines.append(
                _row(
                    f"0x{fpu.fa:08X}",
                    f"0x{fpu.fb:08X}",
                    f"0x{fpu.fpcr:02X}",
                    f"0x{fpu.fpsr:02X}",
                )
            )
            lines.append("</tbody></table>")

        vu: VuRegisters | None = regs.vu
        if vu is not None:
            lines.append(f"<h3 {_H3}>VU Registers</h3>")
            lines.append(f"<table style='{_CSS}'><tbody>")
            lines.append(_row("VA", "VB", "VC", "VM", "VL", "VFPSR", header=True))
            lines.append(
                _row(
                    f"0x{vu.va:04X}",
                    f"0x{vu.vb:04X}",
                    f"0x{vu.vc:04X}",
                    f"0x{vu.vm:04X}",
                    str(vu.vl),
                    f"0x{vu.vfpsr:02X}",
                )
            )
            lines.append("</tbody></table>")

        io_text = cpu.display()
        if io_text:
            lines.append(f"<p style='margin:6px 0'><strong>I/O:</strong> <code>{io_text}</code></p>")

        lines.append("</div>")
        return "".join(lines)

    def _repr_html_(self) -> str:
        return self.to_html()

    def __repr__(self) -> str:
        cpu = self._cpu
        regs = cpu.regs
        lines = [
            f"CPU · {cpu.state.value} · {cpu.steps} steps · {cpu.cycles} cycles",
            f"  A=0x{regs.a:02X}  B=0x{regs.b:02X}  C=0x{regs.c:02X}  D=0x{regs.d:02X}"
            f"  SP=0x{regs.sp:02X}  DP=0x{regs.dp:02X}  IP=0x{regs.ip:02X}",
        ]
        flags_str = " ".join(
            name for name, active in (("Z", regs.flags.z), ("C", regs.flags.c), ("F", regs.flags.f)) if active
        )
        lines.append(f"  FLAGS: {flags_str or '—'}")

        fpu = regs.fpu
        if fpu is not None:
            lines.append(f"  FA=0x{fpu.fa:08X}  FB=0x{fpu.fb:08X}  FPCR=0x{fpu.fpcr:02X}  FPSR=0x{fpu.fpsr:02X}")

        vu = regs.vu
        if vu is not None:
            lines.append(
                f"  VA=0x{vu.va:04X}  VB=0x{vu.vb:04X}  VC=0x{vu.vc:04X}  VM=0x{vu.vm:04X}"
                f"  VL={vu.vl}  VFPSR=0x{vu.vfpsr:02X}"
            )

        io_text = cpu.display()
        if io_text:
            lines.append(f"  I/O: {io_text}")

        return "\n".join(lines)


# ── SimDisplay ───────────────────────────────────────────────────────────────


class SimDisplay:
    """I/O character display (page 0, 0xE8–0xFB) with HTML display.

    Obtained via ``sim.display_output()``.
    """

    def __init__(self, cpu: CPU) -> None:
        self._cpu = cpu

    def to_html(self) -> str:
        """Render as a styled terminal box."""
        text = self._cpu.display()
        escaped = (text or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
        return (
            f"<div style='font-family:monospace;font-size:13px;"
            f"background:#1e1e1e;color:#e0e0e0;padding:6px 14px;"
            f"border-radius:4px;display:inline-block;min-width:240px;"
            f"letter-spacing:0.5px;margin:4px 0'>"
            f"<span style='color:#555;font-size:11px;margin-right:8px'>I/O</span>"
            f"{escaped or '<span style="color:#555">(empty)</span>'}"
            f"</div>"
        )

    def _repr_html_(self) -> str:
        return self.to_html()

    def __repr__(self) -> str:
        return f"Display: {self._cpu.display()!r}"


# ── MemPad ────────────────────────────────────────────────────────────────────

_PAD_TARGET_PX = 256  # target rendered image size in pixels


def _grayscale_png(pixels: list[int], w: int, h: int, scale: int) -> str:
    """Return a base64 PNG data URI for a w×h grayscale image, scaled up."""

    def _chunk(ctype: bytes, data: bytes) -> bytes:
        crc = zlib.crc32(ctype + data) & 0xFFFFFFFF
        return struct.pack(">I", len(data)) + ctype + data + struct.pack(">I", crc)

    rows: list[bytes] = []
    for row_idx in range(h):
        row_px = bytes(pixels[row_idx * w + col] for col in range(w))
        scaled_row = bytes(v for px in row_px for v in [px] * scale)
        for _ in range(scale):
            rows.append(b"\x00" + scaled_row)

    w_out, h_out = w * scale, h * scale
    raw = b"".join(rows)
    png = (
        b"\x89PNG\r\n\x1a\n"
        + _chunk(b"IHDR", struct.pack(">IIBBBBB", w_out, h_out, 8, 0, 0, 0, 0))
        + _chunk(b"IDAT", zlib.compress(raw, 9))
        + _chunk(b"IEND", b"")
    )
    return "data:image/png;base64," + base64.b64encode(png).decode()


class MemPad:
    """Memory region rendered as a pixel/framebuffer grid.

    Each byte maps to one grayscale pixel (0=black, 255=white).
    Obtained via ``sim.pad(addr, w, h)``.
    """

    def __init__(self, mem: Memory, addr: int, w: int, h: int) -> None:
        self._mem = mem
        self._addr = addr & 0xFFFF
        self._w = max(1, w)
        self._h = max(1, h)

    def to_html(self) -> str:
        """Render as an HTML image (PNG data URI)."""
        pixels = [
            self._mem[(self._addr + row * self._w + col) & 0xFFFF] for row in range(self._h) for col in range(self._w)
        ]
        scale = max(1, _PAD_TARGET_PX // max(self._w, self._h))
        uri = _grayscale_png(pixels, self._w, self._h, scale)
        display_size = max(self._w, self._h) * scale
        return (
            f"<div style='font-family:monospace;font-size:13px'>"
            f"<h3 {_H3}>Pad 0x{self._addr:04X}  {self._w}×{self._h}</h3>"
            f"<img src='{uri}' width='{display_size}' height='{display_size}' "
            f"style='image-rendering:pixelated;display:block'>"
            f"</div>"
        )

    def _repr_html_(self) -> str:
        return self.to_html()

    def __repr__(self) -> str:
        lines = [f"Pad 0x{self._addr:04X}  {self._w}×{self._h}"]
        for row in range(self._h):
            row_bytes = [self._mem[(self._addr + row * self._w + col) & 0xFFFF] for col in range(self._w)]
            lines.append("  " + " ".join(f"{b:02X}" for b in row_bytes))
        return "\n".join(lines)


# ── Sim ───────────────────────────────────────────────────────────────────────


class Sim:
    """Interactive sim8 session for Jupyter notebooks.

    Args:
        arch: Architecture version (1=integer, 2=+FPU, 3=+VU). Default 3.

    Example::

        sim = Sim(arch=3)
        sim.asm(\"\"\"
            MOV A, 42
            HLT
        \"\"\")
        sim.state       # registers
        sim.page(0)     # memory page 0
        sim.trace       # execution trace
    """

    def __init__(self, arch: int = 3) -> None:
        self._arch = arch
        self._trace_events: list[TraceEvent] = []
        self._cpu = CPU(arch=arch, tracer=self._trace_events.append)

    # ── Execution ─────────────────────────────────────────────────────────

    def asm(self, source: str) -> SimState:
        """Assemble, load, and run source code. Returns state for display."""
        result = assemble(source, arch=self._arch)
        self._trace_events.clear()
        self._cpu.load(bytes(result.code))
        self._cpu.run()
        return SimState(self._cpu)

    def load(self, code: bytes) -> None:
        """Load binary code (resets CPU and clears trace)."""
        self._trace_events.clear()
        self._cpu.load(code)

    def run(self, max_steps: int = 100_000) -> SimState:
        """Run until HALTED or FAULT. Returns state for display."""
        self._cpu.run(max_steps)
        return SimState(self._cpu)

    def step(self) -> bool:
        """Execute one instruction. Returns True if still RUNNING."""
        return self._cpu.step()

    def reset(self) -> None:
        """Reset CPU and clear trace."""
        self._trace_events.clear()
        self._cpu.reset()

    # ── Display ───────────────────────────────────────────────────────────

    @property
    def state(self) -> SimState:
        """Current CPU state (registers, flags, FPU, VU)."""
        return SimState(self._cpu)

    @property
    def trace(self) -> TraceView:
        """Execution trace collected since last load/asm/reset."""
        return TraceView(list(self._trace_events))

    def page(self, n: int) -> MemPage:
        """Hex dump of memory page *n* (256 bytes starting at n×256)."""
        if not 0 <= n <= 255:
            raise ValueError(f"Page must be 0–255, got {n}")
        return MemPage(self._cpu.mem, n)

    def mem(self, addr: int, n: int = 32) -> MemSlice:
        """Hex dump of *n* bytes starting at *addr*."""
        if not 0 <= addr < MEM_SIZE:
            raise ValueError(f"Address must be 0–0xFFFF, got 0x{addr:X}")
        return MemSlice(self._cpu.mem, addr, n)

    def display_output(self) -> SimDisplay:
        """I/O character display (page 0, 0xE8–0xFB, 20 chars)."""
        return SimDisplay(self._cpu)

    def pad(self, addr: int, w: int = 16, h: int = 0) -> MemPad:
        """Pixel grid view of *w×h* bytes starting at *addr*.

        Each byte is a grayscale pixel (0=black, 255=white).
        If *h* is 0 or omitted, defaults to *w* (square grid).
        """
        if not 0 <= addr < MEM_SIZE:
            raise ValueError(f"Address must be 0–0xFFFF, got 0x{addr:X}")
        return MemPad(self._cpu.mem, addr, w, h if h > 0 else w)

    # ── Direct CPU access ─────────────────────────────────────────────────

    @property
    def cpu(self) -> CPU:
        """Underlying CPU instance for advanced use."""
        return self._cpu

    def __repr__(self) -> str:
        return repr(SimState(self._cpu))
