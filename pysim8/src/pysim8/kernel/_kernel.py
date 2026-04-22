"""sim8 assembly Jupyter kernel.

Each cell is treated as sim8 assembly source.
Magic lines (starting with %) control display and architecture.

Supported magic:
    %arch N              — set architecture (1/2/3), resets sim
    %page N              — show memory page N (256 bytes) after run
    %mem ADDR [N]        — show N bytes at address ADDR after run (default N=32)
    %trace               — show execution trace after run
    %reset               — reset sim without running assembly
    %display             — show I/O character display (page 0, 0xE8–0xFB)
    %pad [ADDR [W [H]]]  — show memory as pixel grid; default ADDR=0x100, W=H=16
"""

from __future__ import annotations

import traceback

from ipykernel.kernelbase import Kernel

from pysim8.asm import AssemblerError
from pysim8.notebook import Sim, SimState

__all__ = ["Sim8Kernel"]

_BANNER = "sim8 assembly kernel  (arch=3: integer + FPU + VU)\nmagic: %arch N  %page N  %mem ADDR [N]  %trace  %reset  %display  %pad [ADDR [W [H]]]"
_VALID_ARCH = (1, 2, 3)


def _parse_addr(s: str) -> int:
    """Parse decimal or 0x-prefixed hex address string."""
    return int(s, 16) if s.startswith("0x") or s.startswith("0X") else int(s)


class Sim8Kernel(Kernel):
    implementation = "sim8"
    implementation_version = "1.0"
    language = "sim8"
    language_version = "3.0"
    language_info = {
        "name": "sim8",
        "mimetype": "text/x-sim8asm",
        "file_extension": ".asm",
        "codemirror_mode": "sim8asm",
        "pygments_lexer": "nasm",
    }
    banner = _BANNER

    def __init__(self, **kwargs: object) -> None:
        super().__init__(**kwargs)  # type: ignore[call-arg]
        self._sim = Sim()

    # ── helpers ───────────────────────────────────────────────────────────

    def _send_html(self, html: str, text: str = "") -> None:
        self.send_response(
            self.iopub_socket,
            "display_data",
            {"data": {"text/html": html, "text/plain": text}, "metadata": {}},
        )

    def _send_text(self, text: str) -> None:
        self.send_response(self.iopub_socket, "stream", {"name": "stdout", "text": text})

    def _send_error(self, msg: str) -> None:
        self.send_response(self.iopub_socket, "stream", {"name": "stderr", "text": msg + "\n"})

    # ── magic parsing ─────────────────────────────────────────────────────

    def _parse_cell(self, code: str) -> tuple[dict[str, list[str]], str]:
        """Split cell into magic directives and assembly source.

        Returns (magics, asm_source) where magics maps command → [args].
        Magic lines must appear before any assembly code.
        """
        magics: dict[str, list[str]] = {}
        asm_lines: list[str] = []
        in_asm = False

        for line in code.splitlines():
            stripped = line.strip()
            if not in_asm and stripped.startswith("%"):
                parts = stripped[1:].split()
                if parts:
                    magics[parts[0].lower()] = parts[1:]
            else:
                in_asm = True
                asm_lines.append(line)

        return magics, "\n".join(asm_lines)

    # ── execute ───────────────────────────────────────────────────────────

    def do_execute(  # type: ignore[override]
        self,
        code: str,
        silent: bool,
        store_history: bool = True,
        user_expressions: object = None,
        allow_stdin: bool = False,
        *,
        cell_id: object = None,
    ) -> dict[str, object]:
        if not code.strip():
            return {"status": "ok", "execution_count": self.execution_count, "payload": [], "user_expressions": {}}

        magics, asm_src = self._parse_cell(code)

        # %arch N — change architecture
        if "arch" in magics:
            args = magics["arch"]
            try:
                arch = int(args[0]) if args else -1
                if arch not in _VALID_ARCH:
                    raise ValueError
                self._sim = Sim(arch=arch)
            except (ValueError, IndexError):
                if not silent:
                    self._send_error(f"%arch: expected 1, 2, or 3 (got {args!r})")

        # %reset — reset without running
        if "reset" in magics:
            self._sim.reset()
            if not silent:
                self._send_text("sim reset\n")
            if not asm_src.strip():
                return {"status": "ok", "execution_count": self.execution_count, "payload": [], "user_expressions": {}}

        # Run assembly (if any)
        if asm_src.strip():
            try:
                state: SimState = self._sim.asm(asm_src)
            except AssemblerError as exc:
                if not silent:
                    self._send_error(f"AssemblerError: {exc}")
                return {
                    "status": "error",
                    "execution_count": self.execution_count,
                    "ename": "AssemblerError",
                    "evalue": str(exc),
                    "traceback": [],
                }
            except Exception:
                if not silent:
                    self._send_error(traceback.format_exc())
                return {
                    "status": "error",
                    "execution_count": self.execution_count,
                    "ename": "RuntimeError",
                    "evalue": "unexpected error",
                    "traceback": [],
                }

            if not silent:
                self._send_html(state.to_html(), repr(state))

                # %page N — full 256-byte page
                if "page" in magics:
                    for arg in magics["page"]:
                        try:
                            self._send_html(self._sim.page(int(arg)).to_html())
                        except (ValueError, IndexError):
                            self._send_error(f"%page: invalid page number {arg!r}")

                # %mem ADDR [N] — arbitrary slice
                if "mem" in magics:
                    args = magics["mem"]
                    try:
                        if not args:
                            raise ValueError("missing address")
                        addr = _parse_addr(args[0])
                        n = int(args[1]) if len(args) > 1 else 32
                        self._send_html(self._sim.mem(addr, n).to_html())
                    except (ValueError, IndexError) as exc:
                        self._send_error(f"%mem: {exc}  usage: %mem ADDR [N]")

                # %trace — execution trace
                if "trace" in magics:
                    self._send_html(self._sim.trace.to_html(), repr(self._sim.trace))

                # %display — I/O character display
                if "display" in magics:
                    d = self._sim.display_output()
                    self._send_html(d.to_html(), repr(d))

                # %pad [ADDR [W [H]]] — pixel framebuffer view
                if "pad" in magics:
                    args = magics["pad"]
                    try:
                        addr = _parse_addr(args[0]) if args else 0x100
                        w = int(args[1]) if len(args) > 1 else 16
                        h = int(args[2]) if len(args) > 2 else w
                        p = self._sim.pad(addr, w, h)
                        self._send_html(p.to_html(), repr(p))
                    except (ValueError, IndexError) as exc:
                        self._send_error(f"%pad: {exc}  usage: %pad [ADDR [W [H]]]")

        return {"status": "ok", "execution_count": self.execution_count, "payload": [], "user_expressions": {}}

    def do_complete(self, code: str, cursor_pos: int) -> dict[str, object]:  # type: ignore[override]
        return {"status": "ok", "matches": [], "cursor_start": cursor_pos, "cursor_end": cursor_pos, "metadata": {}}

    def do_is_complete(self, code: str) -> dict[str, object]:  # type: ignore[override]
        return {"status": "complete"}
