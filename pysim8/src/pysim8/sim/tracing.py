"""Tracing support for CPU simulation."""

from collections.abc import Callable
from dataclasses import dataclass

__all__ = ["TraceEvent", "TraceCallback", "print_tracer", "list_tracer"]

type TraceCallback = Callable[["TraceEvent"], None]


@dataclass(slots=True)
class TraceEvent:
    """Information about a single executed instruction."""

    ip: int
    opcode: int
    operands: tuple[int, ...]
    size: int
    changes: dict[str, int | bool]
    is_fault: bool
    cost: int = 0


def print_tracer(event: TraceEvent) -> None:
    """Print each executed instruction to stdout."""
    parts = [f"IP={event.ip:3d} op={event.opcode:3d}"]
    if event.operands:
        parts.append(f"operands={list(event.operands)}")
    if event.changes:
        parts.append(f"changes={event.changes}")
    if event.cost > 0:
        parts.append(f"cost={event.cost}")
    if event.is_fault:
        parts.append("FAULT")
    print(" ".join(parts))


def list_tracer() -> tuple[list[TraceEvent], TraceCallback]:
    """Return (event_list, callback) for collecting trace events."""
    events: list[TraceEvent] = []
    return events, events.append
