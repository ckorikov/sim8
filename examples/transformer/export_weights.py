#!/usr/bin/env python3
"""Convert trans8 weights.json (fp32) to a flat bf16 binary blob for pysim8.

Reads `<TRANS8_DIR>/out/weights.json` and writes `weights.bin` plus a
human-readable layout map next to this script. Tensor order is fixed and
mirrors `state_dict()` from `trans8.export.export_weights`. Each fp32 is
rounded to bfloat16 (round-half-to-even) and stored little-endian.

The assembly references these tensors via labels at fixed page+offset; the
printed layout map must match the labels in `inference.asm`.
"""

from __future__ import annotations

import json
import struct
from pathlib import Path

TRANS8_WEIGHTS = Path("/Users/ck/dev/2026-spring-efficient-ai/trans8/out/weights.json")
OUT_DIR = Path(__file__).parent
OUT_BIN = OUT_DIR / "weights.bin"
OUT_MAP = OUT_DIR / "weights.layout.txt"

TENSOR_ORDER = [
    "tok_emb.weight",
    "pos_emb.weight",
    "blocks.0.ln1.weight",
    "blocks.0.ln1.bias",
    "blocks.0.attn.qkv.weight",
    "blocks.0.attn.out.weight",
    "blocks.0.ln2.weight",
    "blocks.0.ln2.bias",
    "blocks.0.ffn.up.weight",
    "blocks.0.ffn.down.weight",
    "blocks.1.ln1.weight",
    "blocks.1.ln1.bias",
    "blocks.1.attn.qkv.weight",
    "blocks.1.attn.out.weight",
    "blocks.1.ln2.weight",
    "blocks.1.ln2.bias",
    "blocks.1.ffn.up.weight",
    "blocks.1.ffn.down.weight",
    "ln_f.weight",
    "ln_f.bias",
    "head.weight",
]


def fp32_to_bf16(x: float) -> int:
    """Round-to-nearest-even fp32 → bf16, returning the 16-bit pattern."""
    bits = struct.unpack("<I", struct.pack("<f", x))[0]
    if (bits & 0x7FFFFFFF) > 0x7F800000:  # NaN — preserve quiet bit
        return ((bits >> 16) | 0x0040) & 0xFFFF
    rounding_bias = 0x7FFF + ((bits >> 16) & 1)
    return ((bits + rounding_bias) >> 16) & 0xFFFF


def flatten(tensor) -> list[float]:
    out: list[float] = []

    def rec(t):
        if isinstance(t, list):
            for x in t:
                rec(x)
        else:
            out.append(float(t))

    rec(tensor)
    return out


def main() -> None:
    data = json.loads(TRANS8_WEIGHTS.read_text())
    weights = data["weights"]

    blob = bytearray()
    layout: list[tuple[str, int, int, int]] = []  # name, offset, count, page,off

    for name in TENSOR_ORDER:
        if name not in weights:
            raise KeyError(f"missing tensor {name} in weights.json")
        flat = flatten(weights[name])
        offset = len(blob)
        for x in flat:
            blob += struct.pack("<H", fp32_to_bf16(x))
        layout.append((name, offset, len(flat)))

    OUT_BIN.write_bytes(bytes(blob))

    map_lines = [
        f"# trans8 bf16 weights layout — total {len(blob)} bytes ({len(blob) / 256:.2f} pages)",
        "# columns: tensor, byte_offset, count, page, page_offset",
    ]
    for name, off, n in layout:
        page, page_off = divmod(off, 256)
        map_lines.append(f"{name}\t{off}\t{n}\t{1 + page}\t{page_off}")
    OUT_MAP.write_text("\n".join(map_lines) + "\n")

    print(f"wrote {OUT_BIN} ({len(blob)} bytes)")
    print(f"wrote {OUT_MAP}")
    print()
    print("Layout (page is 1-indexed since weights start at @page 1):")
    for name, off, n in layout:
        page, page_off = divmod(off, 256)
        print(f"  page {1 + page:>3}, off {page_off:>3}  +{2 * n:>4} B  {name}")


if __name__ == "__main__":
    main()
