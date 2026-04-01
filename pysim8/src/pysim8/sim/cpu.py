"""CPU control unit: step/run pipeline and tracing."""

from __future__ import annotations

from typing import TYPE_CHECKING

from pysim8.isa import BY_CODE, BY_CODE_FP, BY_CODE_VU, FP_FMT_WIDTH, ISA, ISA_FP, ISA_VU, InstrDef, Op

from .decoder import Decoder
from .errors import CpuFault, ErrorCode
from .handlers import HandlersMixin
from .handlers_fp import HandlersFpMixin
from .handlers_vu import HandlersVuMixin
from .memory import IO_START, PAGE_SIZE, Memory
from .registers import CpuState, RegisterFile
from .tracing import TraceCallback, TraceEvent

if TYPE_CHECKING:
    from .decoder import DecodedInstr
    from .handlers import Handler

__all__ = ["CPU"]

# FP memory cost by format (fmt = fpm_byte % 8).
# Derived from FP_FMT_WIDTH (bits) / 8, covering fmt 0..4 (v2 valid formats).
# FP_FMT_WIDTH: {0:32, 1:16, 2:16, 3:8, 4:8} → bytes: (4, 2, 2, 1, 1)
_FP_FMT_MEM_COST: tuple[int, ...] = tuple(FP_FMT_WIDTH[fmt] // 8 for fmt in range(5))


class CPU(HandlersMixin, HandlersFpMixin, HandlersVuMixin):
    """8-bit CPU simulator (control unit)."""

    __slots__ = (
        "mem",
        "regs",
        "state",
        "_dispatch",
        "_tracer",
        "_steps",
        "_cycles",
        "_op_cost",
        "_cost_overrides",
        "_arch",
        "_instr_def",
        "_peak_mem",
        "_vu_queue",
    )

    def __init__(
        self,
        *,
        arch: int = 1,
        tracer: TraceCallback | None = None,
        costs: dict[str, int] | None = None,
    ) -> None:
        self.mem = Memory()
        self.regs = RegisterFile(arch=arch)
        self.state = CpuState.IDLE
        self._tracer = tracer
        self._steps = 0
        self._cycles = 0
        self._peak_mem = 0
        self._vwait_pending = False
        self._vwait_size = 0
        self._arch = arch
        self._dispatch: dict[Op, Handler] = {}
        self._build_dispatch()
        if arch >= 2:
            self._build_fp_dispatch()
        if arch >= 3:
            self._build_vu_dispatch()
            self._init_vu()

        overrides = costs or {}
        all_isa = ISA if arch < 2 else ISA + ISA_FP
        if arch >= 3:
            all_isa = all_isa + ISA_VU
        valid = {d.mnemonic for d in all_isa}
        unknown = overrides.keys() - valid
        if unknown:
            raise ValueError(f"Unknown mnemonics in costs: {sorted(unknown)}")
        self._instr_def: dict[int, InstrDef] = {int(d.op): d for d in all_isa}
        self._op_cost: dict[int, int] = {int(d.op): d.cost for d in all_isa if not d.format_dep}
        self._cost_overrides: dict[int, int] = {
            int(d.op): overrides[d.mnemonic] for d in all_isa if d.mnemonic in overrides
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

        # VU ticks at start of step (main clock)
        if self._arch >= 3:
            self.vu_tick()
            # Check VU fault (surfaced at VWAIT or next step)
            if self._vu_queue.fault != 0 and self._vwait_pending:
                code = self._vu_queue.fault
                self._vu_queue.fault = 0
                self._vwait_pending = False
                self._enter_fault(ErrorCode(code))
                return False

        # VWAIT: CPU stalled, only VU ticks
        if self._vwait_pending:
            self._cycles += 1  # stall cost
            if self._vu_queue.fault != 0:
                code = self._vu_queue.fault
                self._vu_queue.fault = 0
                self._vwait_pending = False
                self._enter_fault(ErrorCode(code))
                return False
            if self._vu_queue.is_empty:
                self._vwait_pending = False
                self.regs.ip += self._vwait_size
                self._vwait_size = 0
            return True

        ip_before = self.regs.ip

        try:
            instr = Decoder.fetch(
                self.mem,
                self.regs.ip,
                arch=self._arch,
            )
        except CpuFault as fault:
            self._enter_fault(fault.code)
            if self._tracer is not None:
                opcode = self.mem[ip_before]
                defn = BY_CODE.get(opcode)
                if defn is None and self._arch >= 2:
                    defn = BY_CODE_FP.get(opcode)
                if defn is None and self._arch >= 3:
                    defn = BY_CODE_VU.get(opcode)
                size = defn.size if defn is not None else 1
                self._trace(ip_before, opcode, (), size, {"FF": True, "A": int(fault.code)}, is_fault=True)
            return False

        # HLT: cost=0, not counted in steps/cycles
        if instr.op == Op.HLT:
            self.state = CpuState.HALTED
            return False

        cost = self._compute_cost(instr)
        tracer = self._tracer
        snap_before = self._snapshot() if tracer is not None else {}

        try:
            handler = self._dispatch[instr.op]
            handler(instr)
        except CpuFault as fault:
            self._enter_fault(fault.code)
            if tracer is not None:
                self._trace(
                    ip_before, int(instr.op), instr.operands, instr.size, self._diff(snap_before), is_fault=True
                )
            return False

        self._steps += 1
        self._cycles += cost
        used = self.mem.used_bytes()
        if used > self._peak_mem:
            self._peak_mem = used

        if tracer is not None:
            self._trace(
                ip_before, int(instr.op), instr.operands, instr.size, self._diff(snap_before), is_fault=False, cost=cost
            )

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
        self.regs.reset(arch=self._arch)
        self.state = CpuState.IDLE
        self._steps = 0
        self._cycles = 0
        self._peak_mem = 0
        self._vwait_pending = False
        self._vwait_size = 0
        if self._arch >= 3:
            self._vu_queue.reset()

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

    @property
    def peak_mem(self) -> int:
        """Peak non-zero byte count (excluding I/O region) since last reset."""
        return self._peak_mem

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
        for addr in range(IO_START, PAGE_SIZE):
            b = self.mem[addr]
            chars.append(chr(b) if 0x21 <= b <= 0x7E else " ")
        return "".join(chars).rstrip()

    def __repr__(self) -> str:
        return f"CPU({self.state.value} {self.regs!r})"

    # ── Cost computation ───────────────────────────────────────────────

    def _compute_cost(self, instr: "DecodedInstr") -> int:
        if instr.op in self._cost_overrides:
            return self._cost_overrides[instr.op]
        d = self._instr_def[instr.op]
        if d.format_dep:
            fmt = instr.operands[0] % 8
            return _FP_FMT_MEM_COST[fmt] + d.cost
        return d.cost

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
        if self._tracer is None:
            return
        self._tracer(
            TraceEvent(
                ip=ip,
                opcode=opcode,
                operands=operands,
                size=size,
                changes=changes,
                is_fault=is_fault,
                cost=cost,
            )
        )

    def _snapshot(self) -> dict[str, int | bool]:
        r = self.regs
        snap: dict[str, int | bool] = {
            "A": r.a,
            "B": r.b,
            "C": r.c,
            "D": r.d,
            "SP": r.sp,
            "DP": r.dp,
            "IP": r.ip,
            "ZF": r.flags.z,
            "CF": r.flags.c,
            "FF": r.flags.f,
        }
        if r.fpu is not None:
            snap["FA"] = r.fpu.fa
            snap["FB"] = r.fpu.fb
            snap["FPCR"] = r.fpu.fpcr
            snap["FPSR"] = r.fpu.fpsr
        if r.vu is not None:
            vu = r.vu
            snap["VA"] = vu.va
            snap["VB"] = vu.vb
            snap["VC"] = vu.vc
            snap["VM"] = vu.vm
            snap["VL"] = vu.vl
            snap["VFPSR"] = vu.vfpsr
        return snap

    def _diff(self, before: dict[str, int | bool]) -> dict[str, int | bool]:
        after = self._snapshot()
        return {k: v for k, v in after.items() if v != before[k]}
