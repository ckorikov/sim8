"""Proof harness: prove/check helpers and result tracking."""

from __future__ import annotations

import z3

quiet: bool = False
_failures: list[str] = []
_passed: int = 0


def _ok(label: str) -> None:
    global _passed
    _passed += 1
    if not quiet:
        print(f"  [PROVED] {label}")


def _fail(label: str, model: z3.ModelRef | None = None) -> None:
    msg = f"  [FAIL]   {label}"
    if model is not None:
        msg += f"\n           counterexample: {model}"
    print(msg)
    _failures.append(label)


def prove(claim: z3.BoolRef, *hypotheses: z3.BoolRef, label: str) -> bool:
    """Try to prove `claim` holds under `hypotheses`. Returns True if proved."""
    s = z3.Solver()
    s.add(*hypotheses)
    s.add(z3.Not(claim))
    result = s.check()
    if result == z3.unsat:
        _ok(label)
        return True
    model = s.model() if result == z3.sat else None
    _fail(label, model)
    return False


def check(condition: bool, label: str) -> bool:
    """Assert a Python-level invariant."""
    if condition:
        _ok(label)
        return True
    _fail(label)
    return False


def results() -> tuple[int, list[str]]:
    """Return (passed_count, failure_labels)."""
    return _passed, list(_failures)
