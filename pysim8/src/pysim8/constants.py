"""Shared constants for memory layout and FP format codes.

Leaf module — no pysim8 internal imports. Safe to import from anywhere.
"""

# ── Memory layout ────────────────────────────────────────────────
MEM_SIZE = 65536
PAGE_SIZE = 256
IO_START = 232
SP_INIT = 231

# ── FP format codes (spec §fp.md) ───────────────────────────────
FP_FMT_F = 0  # float32 (E8M23), 32-bit
FP_FMT_H = 1  # float16 (E5M10), 16-bit
FP_FMT_BF = 2  # bfloat16 (E8M7), 16-bit
FP_FMT_O3 = 3  # OFP8 E4M3, 8-bit
FP_FMT_O2 = 4  # OFP8 E5M2, 8-bit
FP_FMT_N1 = 5  # 4-bit E2M1 (reserved in v2)
FP_FMT_N2 = 6  # 4-bit E1M2 (reserved in v2)

FP_FMT_WIDTH: dict[int, int] = {
    FP_FMT_F: 32,
    FP_FMT_H: 16,
    FP_FMT_BF: 16,
    FP_FMT_O3: 8,
    FP_FMT_O2: 8,
    FP_FMT_N1: 4,
    FP_FMT_N2: 4,
}

FP_FMT_MAX_POS: dict[int, int] = {
    FP_FMT_F: 0,
    FP_FMT_H: 1,
    FP_FMT_BF: 1,
    FP_FMT_O3: 3,
    FP_FMT_O2: 3,
    FP_FMT_N1: 7,
    FP_FMT_N2: 7,
}
