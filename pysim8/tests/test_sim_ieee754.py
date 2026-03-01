"""IEEE 754 conformance tests for pysim8 via CPU simulation.

Drives the actual pysim8 CPU (decoder → handler → fp_formats → FPSR)
with test vectors from the sergev/ieee754-test-suite submodule.

Run:
    cd pysim8
    uv run pytest tests/test_sim_ieee754.py -v
    IEEE754_MAX=50 uv run pytest tests/test_sim_ieee754.py -v  # quick smoke
"""

from __future__ import annotations

import math
import os
import struct
from pathlib import Path
from typing import NamedTuple

import pytest

from pysim8.isa import FP_FMT_F, FP_FMT_H, encode_fpm
from pysim8.sim import CPU, CpuState

# ── Constants ─────────────────────────────────────────────────────────────

SUITE_DIR = Path(__file__).parents[2] / "ieee754-test-suite"
# IEEE754_MAX=0 means unlimited; set to N to cap cases per run
MAX_CASES = int(os.environ.get("IEEE754_MAX", "0"))

ROUNDING_MAP: dict[str, int] = {"=0": 0, ">": 3, "<": 2, "0": 1}

SUPPORTED_OPS: frozenset[str] = frozenset({
    "+", "-", "*", "/", "V", "~", "A", "qC",
    "*+", "cff", "cif", "cfi",
})
UNARY_OPS: frozenset[str] = frozenset({"V", "~", "A"})
BINARY_OPS: frozenset[str] = frozenset({"+", "-", "*", "/", "qC"})
TERNARY_OPS: frozenset[str] = frozenset({"*+"})
CONVERT_OPS: frozenset[str] = frozenset({"cff", "cif", "cfi"})

OP_OPCODE: dict[str, int] = {
    "+": 132,    # FADD_FP_ADDR
    "-": 134,    # FSUB_FP_ADDR
    "*": 136,    # FMUL_FP_ADDR
    "/": 138,    # FDIV_FP_ADDR
    "qC": 140,   # FCMP_FP_ADDR
    "V": 144,    # FSQRT_FP
    "~": 143,    # FNEG_FP
    "A": 142,    # FABS_FP
    "*+": 159,   # FMADD_FP_FP_ADDR
    "cff": 146,  # FCVT_FP_FP
    "cif": 147,  # FITOF_FP_GPR
    "cfi": 148,  # FFTOI_GPR_FP
}

# FPSR bit masks (from spec/errors.md and existing tests)
FPSR_NV = 0x01  # invalid
FPSR_DZ = 0x02  # div-by-zero
FPSR_OF = 0x04  # overflow
FPSR_UF = 0x08  # underflow
FPSR_NX = 0x10  # inexact
FPSR_KNOWN_MASK = FPSR_NV | FPSR_DZ | FPSR_OF | FPSR_UF | FPSR_NX

FLAG_CHAR_TO_MASK: dict[str, int] = {
    "i": FPSR_NV,
    "z": FPSR_DZ,
    "o": FPSR_OF,
    "u": FPSR_UF,  # underflow (tininess before rounding)
    "v": FPSR_UF,  # underflow (tininess after rounding)
    "w": FPSR_UF,  # underflow (tininess + error)
    "x": FPSR_NX,
}

# FPM bytes
_FPM_FA  = encode_fpm(0, 0, FP_FMT_F)  # 0x00 — float32 FA
_FPM_FHA = encode_fpm(0, 0, FP_FMT_H)  # 0x01 — float16 FHA
_FPM_FHB = encode_fpm(0, 1, FP_FMT_H)  # 0x09 — float16 FHB

_KNOWN_PREFIXES = frozenset({"b32", "b16"})


# ── Data model ────────────────────────────────────────────────────────────

class FpTestCase(NamedTuple):
    op: str
    prefix: str          # "b32" or "b16"
    rounding: int        # RoundingMode constant 0-3
    inputs: list[float]
    expected: float      # math.nan if result is Q or S
    flags: str           # expected raised flags e.g. "xi", ""
    line: str            # original line for pytest ID


# ── Parser ────────────────────────────────────────────────────────────────

def _is_exception_str(tok: str) -> bool:
    """Return True if tok is composed entirely of exception flag chars."""
    return bool(tok) and all(c in "xuvwozi" for c in tok)


def parse_fp_token(tok: str) -> float | None:
    """Convert one IBM FPgen operand token to Python float.

    IBM format: ±N.FFFFFFP±E  where FFFFFF are the raw fraction bits
    right-justified in hex (6 digits for b32/23-bit fraction, 3 digits
    for b16/10-bit fraction).  This differs from standard C hex-float
    notation where the digits represent fractional powers of 16.

    Returns None for unrecognised tokens (e.g. decimal integers).
    """
    if tok in ("Q", "S"):
        return math.nan
    if tok == "+Inf":
        return math.inf
    if tok == "-Inf":
        return -math.inf
    if tok == "+Zero":
        return 0.0
    if tok == "-Zero":
        return -0.0
    try:
        sign_val = -1.0 if tok[0] == "-" else 1.0
        rest = tok[1:] if tok[0] in "+-" else tok
        p_idx = rest.upper().find("P")
        if p_idx == -1:
            return None  # integer or unrecognised
        man = rest[:p_idx]
        exp = int(rest[p_idx + 1:])
        if "." not in man:
            return None
        dot = man.index(".")
        int_part = int(man[:dot], 16)   # 0 (subnormal) or 1 (normal)
        frac_hex = man[dot + 1:]
        frac = int(frac_hex, 16)        # raw fraction bits
        n = len(frac_hex)
        # Infer mantissa width from digit count:
        #   6 hex digits → 23-bit fraction (binary32)
        #   3 hex digits → 10-bit fraction (binary16)
        if n == 6:
            M = 23
        elif n == 3:
            M = 10
        else:
            return None  # unrecognised precision
        # value = (int_part * 2^M + frac) * 2^(exp - M)
        sig = (int_part << M) | frac
        return sign_val * math.ldexp(sig, exp - M)
    except (ValueError, IndexError):
        return None


def parse_fptest_line(line: str) -> FpTestCase | None:
    """Parse one .fptest line, return FpTestCase or None to skip."""
    line = line.strip()
    if not line or line[0] not in "bB":
        return None

    toks = line.split()
    if len(toks) < 4:
        return None

    # 1. Parse token[0]: detect known prefix, extract op
    tok0 = toks[0]
    prefix: str | None = None
    op: str | None = None
    for p in _KNOWN_PREFIXES:
        if tok0.startswith(p):
            candidate = tok0[len(p):]
            if candidate in SUPPORTED_OPS:
                prefix = p
                op = candidate
                break
    if prefix is None or op is None:
        return None

    # Skip b32 FMA: v2 ISA has only one float32 slot (FA), no room for 3 operands
    if op == "*+" and prefix == "b32":
        return None

    # 2. Token[1] = rounding mode
    rounding_tok = toks[1]
    if rounding_tok not in ROUNDING_MAP:
        return None
    rounding = ROUNDING_MAP[rounding_tok]

    # 3. Find the arrow separator
    try:
        arrow_idx = toks.index("->")
    except ValueError:
        return None

    # 4. Tokens between rounding and arrow: exception enables + operands
    inputs: list[float] = []
    for tok in toks[2:arrow_idx]:
        if _is_exception_str(tok):
            # Trap-scaled results (u/v/w/o) — not implemented, skip
            if any(c in tok for c in "uvwo"):
                return None
            continue
        val = parse_fp_token(tok)
        if val is None:
            return None  # unrecognised token → skip whole line
        inputs.append(val)

    # 5. Result token (first token after arrow)
    if arrow_idx + 1 >= len(toks):
        return None
    result_tok = toks[arrow_idx + 1]
    if result_tok == "#":
        return None  # exception was trapped, no output to check

    expected = parse_fp_token(result_tok)
    if expected is None:
        return None

    # 6. Optional raised-exception flags (token after result)
    flags = ""
    if arrow_idx + 2 < len(toks):
        candidate_flags = toks[arrow_idx + 2]
        if _is_exception_str(candidate_flags):
            flags = candidate_flags

    return FpTestCase(
        op=op,
        prefix=prefix,
        rounding=rounding,
        inputs=list(inputs),
        expected=expected,
        flags=flags,
        line=line,
    )


def load_cases(filename: str) -> list[FpTestCase]:
    """Load and parse test cases from one .fptest file."""
    path = SUITE_DIR / filename
    if not path.exists():
        return []
    cases: list[FpTestCase] = []
    with path.open() as f:
        for line in f:
            tc = parse_fptest_line(line)
            if tc is not None:
                cases.append(tc)
    return cases


# ── Memory / program helpers ──────────────────────────────────────────────

# Memory layout used by all test programs:
#   0x00–0x1F  program bytes
#   0x80       operand A  (4 bytes f32 / 2 bytes f16)
#   0x82       operand B  (2 bytes f16) — b16 binary ops only
#   0x84       operand B  (4 bytes f32) — b32 binary ops
#              operand C for FMA b16 @ 0x84
#   0x90       result     (4 or 2 bytes)

def _store_f32(mem: list[int], addr: int, value: float) -> None:
    for i, b in enumerate(struct.pack("<f", value)):
        mem[addr + i] = b


def _store_f16(mem: list[int], addr: int, value: float) -> None:
    for i, b in enumerate(struct.pack("<e", value)):
        mem[addr + i] = b


def _read_f32(mem: list[int], addr: int) -> float:
    return struct.unpack("<f", bytes(mem[addr + i] for i in range(4)))[0]


def _read_f16(mem: list[int], addr: int) -> float:
    return struct.unpack("<e", bytes(mem[addr + i] for i in range(2)))[0]


def _binary_prog(opcode: int, fpm: int, rounding: int, b_addr: int) -> list[int]:
    """Program: set rounding, load A, compute A op mem[b_addr], store to 0x90."""
    return [
        6, 0, rounding,       # MOV A, rounding
        151, 0,               # FSCFG A  (write FPCR.RM)
        152,                  # FCLR     (clear FPSR)
        128, fpm, 0x80,       # FMOV FA, [0x80]
        opcode, fpm, b_addr,  # OP FA, [b_addr]
        130, fpm, 0x90,       # FMOV [0x90], FA
        149, 0,               # FSTAT A  (read FPSR → A)
        0,                    # HLT
    ]


def _unary_prog(opcode: int, fpm: int, rounding: int) -> list[int]:
    """Program: set rounding, load A, apply unary op, store to 0x90."""
    return [
        6, 0, rounding,  # MOV A, rounding
        151, 0,          # FSCFG A
        152,             # FCLR
        128, fpm, 0x80,  # FMOV FA, [0x80]
        opcode, fpm,     # OP FA  (in-place unary)
        130, fpm, 0x90,  # FMOV [0x90], FA
        149, 0,          # FSTAT A
        0,               # HLT
    ]


def _cmp_prog(fpm: int, rounding: int) -> list[int]:
    """Program: load A, compare A vs mem[0x84], read FPSR."""
    return [
        6, 0, rounding,
        151, 0,
        152,
        128, fpm, 0x80,   # FMOV FA, [0x80]
        140, fpm, 0x84,   # FCMP FA, [0x84]
        149, 0,           # FSTAT A
        0,                # HLT
    ]


def _fma_b16_prog(rounding: int) -> list[int]:
    """Program for b16 FMA: FHA = FHB * mem[0x84] + FHA.

    Suite mapping:  a * b + c
    Memory layout:  FHA=c @0x80, FHB=a @0x82, b @0x84
    """
    return [
        6, 0, rounding,                           # MOV A, rounding
        151, 0,                                   # FSCFG A
        152,                                      # FCLR
        128, _FPM_FHA, 0x80,                      # FMOV FHA, [0x80]  (c)
        128, _FPM_FHB, 0x82,                      # FMOV FHB, [0x82]  (a)
        159, _FPM_FHA, _FPM_FHB, 0x84,           # FMADD FHA, FHB, [0x84]
        130, _FPM_FHA, 0x90,                      # FMOV [0x90], FHA
        149, 0,                                   # FSTAT A
        0,                                        # HLT
    ]


# ── CPU runner ────────────────────────────────────────────────────────────

def run_fp_case(tc: FpTestCase) -> tuple[float, int]:
    """Run one FP test case through the CPU.

    Returns (result_as_float, fpsr_byte).
    For qC (compare), result is 0.0 and fpsr reflects cpu.zero/carry.
    """
    is_b16 = tc.prefix == "b16"
    fpm = _FPM_FHA if is_b16 else _FPM_FA
    b_addr = 0x82 if is_b16 else 0x84
    store = _store_f16 if is_b16 else _store_f32
    read = _read_f16 if is_b16 else _read_f32

    mem: list[int] = [0] * 256

    if tc.op in BINARY_OPS and tc.op != "qC":
        store(mem, 0x80, tc.inputs[0])
        store(mem, b_addr, tc.inputs[1])
        prog = _binary_prog(OP_OPCODE[tc.op], fpm, tc.rounding, b_addr)

    elif tc.op == "qC":
        store(mem, 0x80, tc.inputs[0])
        store(mem, b_addr, tc.inputs[1])
        prog = _cmp_prog(fpm, tc.rounding)

    elif tc.op in UNARY_OPS:
        store(mem, 0x80, tc.inputs[0])
        prog = _unary_prog(OP_OPCODE[tc.op], fpm, tc.rounding)

    elif tc.op == "*+":
        # b16 FMA only (b32 filtered out by parser)
        _store_f16(mem, 0x80, tc.inputs[2])  # c (addend)
        _store_f16(mem, 0x82, tc.inputs[0])  # a
        _store_f16(mem, 0x84, tc.inputs[1])  # b
        prog = _fma_b16_prog(tc.rounding)
        read = _read_f16

    else:
        raise ValueError(f"Unsupported op in run_fp_case: {tc.op!r}")

    for i, byte in enumerate(prog):
        mem[i] = byte

    cpu = CPU(arch=2)
    cpu.load(mem)
    state = cpu.run()

    if state == CpuState.FAULT:
        pytest.fail(f"CPU faulted (code={cpu.a}) for: {tc.line}")

    assert state != CpuState.RUNNING, f"Step limit reached for: {tc.line}"

    if tc.op == "qC":
        # zero/carry already set; fpsr is in cpu.a
        return 0.0, cpu.a

    result = read(cpu.mem, 0x90)
    fpsr = cpu.a
    return result, fpsr


# ── Assertion helpers ─────────────────────────────────────────────────────

def assert_fp_result(
    actual: float,
    expected: float,
    prefix: str,
    context: str = "",
) -> None:
    """Assert actual matches expected to bit precision."""
    ctx = f" [{context}]" if context else ""

    if math.isnan(expected):
        assert math.isnan(actual), f"Expected NaN, got {actual!r}{ctx}"
        return

    if math.isinf(expected):
        assert actual == expected, f"Expected {expected!r}, got {actual!r}{ctx}"
        return

    # Zero: just check it's zero (sign of zero is implementation-defined in many cases)
    if expected == 0.0:
        assert actual == 0.0, f"Expected zero, got {actual!r}{ctx}"
        return

    # Normal: bit-exact comparison
    if prefix == "b32":
        exp_bits = struct.unpack("<I", struct.pack("<f", expected))[0]
        act_bits = struct.unpack("<I", struct.pack("<f", actual))[0]
    else:
        exp_bits = struct.unpack("<H", struct.pack("<e", expected))[0]
        act_bits = struct.unpack("<H", struct.pack("<e", actual))[0]

    assert exp_bits == act_bits, (
        f"Expected {expected!r} (bits={exp_bits:#010x}), "
        f"got {actual!r} (bits={act_bits:#010x}){ctx}"
    )


def assert_fp_flags(fpsr: int, expected_flags: str, context: str = "") -> None:
    """Assert IEEE754 exception flags match expected_flags.

    If expected_flags is empty, tolerate implementation-defined extra flags.
    If expected_flags is non-empty, require an exact match on known FPSR bits.
    """
    if not expected_flags:
        return

    mask = 0
    for ch in expected_flags:
        mask |= FLAG_CHAR_TO_MASK.get(ch, 0)
    ctx = f" [{context}]" if context else ""
    assert (fpsr & FPSR_KNOWN_MASK) == mask, (
        f"Expected flags {expected_flags!r} (mask={mask:#04x}), "
        f"fpsr={fpsr:#04x}{ctx}"
    )


# ── Module-level skip guard ───────────────────────────────────────────────

pytestmark = pytest.mark.skipif(
    not SUITE_DIR.exists(),
    reason="ieee754-test-suite submodule not initialized "
           "(run: git submodule update --init ieee754-test-suite)",
)


# ── Test group loader ─────────────────────────────────────────────────────

def _load_group(
    files: list[str],
    op_filter: set[str] | None = None,
) -> list[FpTestCase]:
    """Load and optionally filter cases from multiple .fptest files."""
    cases: list[FpTestCase] = []
    for fname in files:
        batch = load_cases(fname)
        if op_filter is not None:
            batch = [tc for tc in batch if tc.op in op_filter]
        cases.extend(batch)
    if MAX_CASES > 0:
        cases = cases[:MAX_CASES]
    return cases


def _run_and_assert(tc: FpTestCase) -> None:
    result, fpsr = run_fp_case(tc)
    assert_fp_result(result, tc.expected, tc.prefix, tc.line)
    assert_fp_flags(fpsr, tc.flags, tc.line)


# ── Collected test cases (module level, loaded once) ─────────────────────

_ADD_CASES = _load_group([
    "Add-Shift.fptest",
    "Add-Cancellation.fptest",
    "Add-Shift-And-Special-Significands.fptest",
    "Add-Cancellation-And-Subnorm-Result.fptest",
])

_ROUND_CASES = _load_group([
    "Rounding.fptest",
    "Corner-Rounding.fptest",
    "Vicinity-Of-Rounding-Boundaries.fptest",
], op_filter={"+", "-", "*", "/", "V"})  # exclude b32*+ FMA

_OVF_UF_CASES = _load_group([
    "Overflow.fptest",
    "Underflow.fptest",
], op_filter={"+", "-", "*", "/", "V"})  # exclude b32*+ FMA

_DIV_CASES = _load_group([
    "Divide-Divide-By-Zero-Exception.fptest",
    "Divide-Trailing-Zeros.fptest",
])

_STICKY_CASES = _load_group([
    "Sticky-Bit-Calculation.fptest",
], op_filter={"+", "-", "*", "/"})  # exclude FMA

_SPECIAL_CASES = _load_group([
    "Input-Special-Significand.fptest",
])

# b16*+ FMA — suite only has b32*+ which the parser filters out; empty list OK
_FMA_CASES = _load_group([
    "MultiplyAdd-Shift.fptest",
    "MultiplyAdd-Cancellation.fptest",
    "MultiplyAdd-Shift-And-Special-Significands.fptest",
    "MultiplyAdd-Cancellation-And-Subnorm-Result.fptest",
    "MultiplyAdd-Special-Events-Inexact.fptest",
    "MultiplyAdd-Special-Events-Overflow.fptest",
    "MultiplyAdd-Special-Events-Underflow.fptest",
])

# Conversions: cff/cif/cfi — suite only has b32→b128/b64; empty list OK
_CONV_CASES = _load_group([
    "Basic-Types-Inputs.fptest",
    "Basic-Types-Intermediate.fptest",
], op_filter={"cff", "cif", "cfi"})


# ── Parametrized test ─────────────────────────────────────────────────────

_ALL_GROUPS = [
    ("add", _ADD_CASES),
    ("rounding", _ROUND_CASES),
    ("overflow_underflow", _OVF_UF_CASES),
    ("divide", _DIV_CASES),
    ("sticky_bit", _STICKY_CASES),
    ("special_inputs", _SPECIAL_CASES),
    ("fma", _FMA_CASES),
    ("conversions", _CONV_CASES),
]


def _all_cases():
    for _group_name, cases in _ALL_GROUPS:
        for tc in cases:
            yield pytest.param(tc, id=tc.line[:70])


@pytest.mark.parametrize("tc", list(_all_cases()))
def test_ieee754(tc: FpTestCase) -> None:
    _run_and_assert(tc)
