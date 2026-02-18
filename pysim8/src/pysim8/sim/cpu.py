"""CPU control unit: step/run pipeline and tracing."""

from __future__ import annotations

from typing import TYPE_CHECKING

from pysim8.isa import BY_CODE, ISA, Op

from .decoder import Decoder
from .errors import CpuFault, ErrorCode
from .handlers import HandlersMixin
from .memory import Memory
from .registers import CpuState, RegisterFile
from .tracing import TraceCallback, TraceEvent

if TYPE_CHECKING:
    from .handlers import Handler

__all__ = ["CPU"]


class CPU(HandlersMixin):
    """8-bit CPU simulator (control unit)."""

    __slots__ = (
        "mem", "regs", "state", "_dispatch", "_tracer",
        "_steps", "_cycles", "_op_cost",
    )

    def __init__(
        self,
        *,
        tracer: TraceCallback | None = None,
        costs: dict[str, int] | None = None,
    ) -> None:
        self.mem = Memory()
        self.regs = RegisterFile()
        self.state = CpuState.IDLE
        self._tracer = tracer
        self._steps = 0
        self._cycles = 0
        self._dispatch: dict[Op, Handler] = {}
        self._build_dispatch()

        overrides = costs or {}
        valid = {d.mnemonic for d in ISA}
        unknown = overrides.keys() - valid
        if unknown:
            raise ValueError(f"Unknown mnemonics in costs: {sorted(unknown)}")
        self._op_cost: dict[int, int] = {
            int(d.op): overrides.get(d.mnemonic, d.cost)
            for d in ISA
        }

    # ── Public API ─────────────────────────────────────────────────────

    def load(self, code: bytes | list[int]) -> None:
        """Reset CPU and load code into memory."""
        self.reset()
        self.mem.load(code)

    def step(self) -> bool:
        """Execute one instruction. Returns True if still RUNNING."""
        if self.state in (CpuState.FAULT, CpuState.HALTED):
            return False

        if self.state == CpuState.IDLE:
            self.state = CpuState.RUNNING

        ip_before = self.regs.ip

        try:
            insn = Decoder.fetch(self.mem, self.regs.ip)
        except CpuFault as fault:
            self._enter_fault(fault.code)
            if self._tracer is not None:
                opcode = self.mem[ip_before]
                defn = BY_CODE.get(opcode)
                size = defn.size if defn is not None else 1
                self._trace(ip_before, opcode, (), size,
                            {"FF": True, "A": int(fault.code)},
                            is_fault=True)
            return False

        # HLT: cost=0, not counted in steps/cycles
        if insn.op == Op.HLT:
            self.state = CpuState.HALTED
            return False

        tracer = self._tracer
        snap_before = self._snapshot() if tracer is not None else {}

        try:
            handler = self._dispatch[insn.op]
            handler(insn)
        except CpuFault as fault:
            self._enter_fault(fault.code)
            if tracer is not None:
                self._trace(ip_before, int(insn.op), insn.operands,
                            insn.size, self._diff(snap_before),
                            is_fault=True)
            return False

        cost = self._op_cost[int(insn.op)]
        self._steps += 1
        self._cycles += cost

        if tracer is not None:
            self._trace(ip_before, int(insn.op), insn.operands,
                        insn.size, self._diff(snap_before),
                        is_fault=False, cost=cost)

        return self.state == CpuState.RUNNING

    def run(self, max_steps: int = 100_000) -> CpuState:
        """Run until HALTED or FAULT (or max_steps exceeded).

        Returns the final state. If RUNNING, the step limit was reached
        without halting — likely an infinite loop.
        """
        for _ in range(max_steps):
            if not self.step():
                break
        return self.state

    def reset(self) -> None:
        """Reset CPU to IDLE state."""
        self.mem.reset()
        self.regs.reset()
        self.state = CpuState.IDLE
        self._steps = 0
        self._cycles = 0

    @property
    def tracer(self) -> TraceCallback | None:
        return self._tracer

    @tracer.setter
    def tracer(self, cb: TraceCallback | None) -> None:
        self._tracer = cb

    @property
    def steps(self) -> int:
        return self._steps

    @property
    def cycles(self) -> int:
        return self._cycles

    # Convenience properties
    @property
    def a(self) -> int:
        return self.regs.a

    @property
    def b(self) -> int:
        return self.regs.b

    @property
    def c(self) -> int:
        return self.regs.c

    @property
    def d(self) -> int:
        return self.regs.d

    @property
    def sp(self) -> int:
        return self.regs.sp

    @property
    def dp(self) -> int:
        return self.regs.dp

    @property
    def ip(self) -> int:
        return self.regs.ip

    @property
    def zero(self) -> bool:
        return self.regs.flags.z

    @property
    def carry(self) -> bool:
        return self.regs.flags.c

    @property
    def fault(self) -> bool:
        return self.regs.flags.f

    def display(self) -> str:
        """Read console I/O region (page 0, addresses 232-255).

        Per spec: non-printable and whitespace characters render as space.
        Trailing spaces (from unwritten cells) are stripped.
        """
        chars: list[str] = []
        for addr in range(Memory.IO_START, Memory.PAGE_SIZE):
            b = self.mem[addr]
            chars.append(chr(b) if 0x21 <= b <= 0x7E else " ")
        return "".join(chars).rstrip()

    def __repr__(self) -> str:
        return f"CPU({self.state.value} {self.regs!r})"

    # ── Fault handling ─────────────────────────────────────────────────

    def _enter_fault(self, code: ErrorCode) -> None:
        self.regs.flags.f = True
        self.regs.a = int(code)
        self.state = CpuState.FAULT

    # ── Tracer helpers ─────────────────────────────────────────────────

    def _trace(
        self,
        ip: int,
        opcode: int,
        operands: tuple[int, ...],
        size: int,
        changes: dict[str, int | bool],
        *,
        is_fault: bool,
        cost: int = 0,
    ) -> None:
        assert self._tracer is not None
        self._tracer(TraceEvent(
            ip=ip, opcode=opcode, operands=operands,
            size=size, changes=changes,
            is_fault=is_fault, cost=cost,
        ))

    def _snapshot(self) -> dict[str, int | bool]:
        r = self.regs
        return {
            "A": r.a, "B": r.b, "C": r.c, "D": r.d,
            "SP": r.sp, "DP": r.dp, "IP": r.ip,
            "ZF": r.flags.z, "CF": r.flags.c, "FF": r.flags.f,
        }

    def _diff(self, before: dict[str, int | bool]) -> dict[str, int | bool]:
        after = self._snapshot()
        return {k: v for k, v in after.items() if v != before[k]}
