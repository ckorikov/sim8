#!/usr/bin/env python3
"""Convert any image to grayscale BMP (8-bit) for sim8 pad viewer.

Usage:
    python3 convert.py input.png                       # → input_8bpp.bmp (28×28)
    python3 convert.py input.png -o out.bmp --size 64  # → 64×64

Supports PNG, JPEG, BMP, etc. (via Pillow).
Output is standard bottom-up 8bpp grayscale BMP with 256-color palette.
"""

import sys


def convert(src_path: str, dst_path: str | None, size: int) -> None:
    try:
        from PIL import Image
    except ImportError:
        print("pip install Pillow  (required for PNG/JPEG)", file=sys.stderr)
        sys.exit(1)

    img = Image.open(src_path).convert("L")
    img = img.resize((size, size), Image.LANCZOS)

    if dst_path is None:
        dst_path = src_path.rsplit(".", 1)[0] + "_8bpp.bmp"

    img.save(dst_path)
    print(f"→ {dst_path} ({size}x{size} 8bpp)")


if __name__ == "__main__":
    import argparse

    p = argparse.ArgumentParser(description="Convert image to grayscale BMP for sim8 pad.")
    p.add_argument("input", help="Source image (PNG, JPEG, BMP, etc.)")
    p.add_argument("-o", "--output", help="Output path (default: input_8bpp.bmp)")
    p.add_argument("--size", type=int, default=28, help="Resize to NxN (default: 28)")
    args = p.parse_args()
    convert(args.input, args.output, args.size)
