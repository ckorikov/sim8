"""Z3 formal verification of sim8 ISA encoding schemes.

Proves correctness of the four byte-packing encodings defined in spec/isa.json
using Z3 SMT solver, then cross-checks the JSON data for structural consistency.

Usage:
    uv run verify.py           # from formal/z3/
    uv run verify.py --quiet   # suppress [PROVED] lines, show only failures

Proof obligations:
    REGADDR  — roundtrip, injectivity, output-fits-byte, reg-field preserved,
               right-inverse: encode(decode(b)) == b (universal),
               DP (code 5) outside valid domain
    FPM      — roundtrip, injectivity, structural bound (byte ≤ 0x7E),
               right-inverse: encode(decode(b)) == b (universal),
               30 named registers have distinct bytes
    VFM      — roundtrip, injectivity, upper-3-bits always zero,
               left-inverse: encode(decode(b)) == b & 0x1F
    VU_REGS  — roundtrip, injectivity, lower-2-bits always zero,
               left-inverse: encode(decode(b)) == b & 0xFC

Data checks (isa.json consistency):
    D1   opcode uniqueness across all tables
    D2   opcode ranges: core 0-127, FP 128-162, VU 163-183
    D3   VU format codes 0-6 in order
    D4   VU mode codes 0-3 in order
    D5   VU condition codes 0-5 in order
    D6   FP register FPM bytes are distinct
    D7   FP register (pos, fmt) validity per FP_FMT_MAX_POS
    D8   FP format widths match constants
    D9   VU elem_size matches constants
    D10  Instruction size calculation in [1,4] (current max; spec reserves up to 7)
    D11  Every VU instruction is sync or async, exactly 7 sync
    D12  FP format codes 0-6 in order; max_pos matches constants
    D13  since field: core=1, FP=2, VU=3
    D14  All operand types from the known set
    D15  All instruction costs ≥ 0
    D16  VU operand structure: async binary=2, VCMP=3, sync per fixed table
    D17  Mnemonic aliases resolve to existing mnemonics
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import fpm
import harness
import isa_checks
import regaddr
import vfm
import vu_regs

_REPO = Path(__file__).parent.parent.parent
_ISA_JSON = _REPO / "spec" / "isa.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--quiet", action="store_true", help="Only print failures")
    args = parser.parse_args()
    harness.quiet = args.quiet

    isa = json.loads(_ISA_JSON.read_text())

    regaddr.verify()
    fpm.verify(isa)
    vfm.verify()
    vu_regs.verify()
    isa_checks.verify(isa)

    passed, failures = harness.results()
    total = passed + len(failures)

    print(f"{'─' * 50}")
    print(f"  {passed}/{total} passed", end="")
    if failures:
        print(f"  ← {len(failures)} FAILED:")
        for f in failures:
            print(f"    • {f}")
        return 1
    print("  ✓ all passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
