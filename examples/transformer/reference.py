#!/usr/bin/env python3
"""Numpy reference forward for the trans8 GPT, used to verify inference.asm.

Mirrors `trans8.model.GPT.forward` but in pure numpy and quantizes weights to
bfloat16 to match the on-device representation. The polynomial exp/tanh used
here also matches the assembly so intermediate values can be compared during
debugging.
"""

from __future__ import annotations

import json
import struct
from pathlib import Path

import numpy as np

TRANS8_WEIGHTS = Path("/Users/ck/dev/2026-spring-efficient-ai/trans8/out/weights.json")

# Sequence used by inference.asm. Pattern length is 5; the model is shown
# pat + pat[:-1] (9 tokens) and should predict pat shifted by 1, so positions
# 4..8 of the output should be pat[0..4] = [0, 1, 2, 3, 0].
PATTERN = [0, 1, 2, 3, 0]
INPUT_TOKENS = PATTERN + PATTERN[:-1]  # 9 tokens
VOCAB_CHARS = "ABCD"


def fp32_to_bf16_bits(x: np.ndarray) -> np.ndarray:
    bits = x.astype(np.float32).view(np.uint32).copy()
    is_nan = (bits & 0x7FFFFFFF) > 0x7F800000
    rounding_bias = 0x7FFF + ((bits >> 16) & 1)
    out = np.where(is_nan, (bits >> 16) | 0x0040, (bits + rounding_bias) >> 16)
    return out.astype(np.uint16)


def quantize_bf16(x: np.ndarray) -> np.ndarray:
    """Round fp32 → bf16 → fp32 (bit-equivalent to the on-device value)."""
    bits = fp32_to_bf16_bits(x)
    fp32_bits = bits.astype(np.uint32) << 16
    return fp32_bits.view(np.float32).astype(np.float32)


def poly_exp_neg(x: np.ndarray) -> np.ndarray:
    """Polynomial exp(x) for x <= 0. Matches the routine in inference.asm.

    Range-reduces x = k*ln2 + r with r in [-ln2, 0], approximates
    exp(r) ≈ 1 + r + r²/2 + r³/6, then multiplies by 2**k.
    Returns 0 for x < -10.
    """
    x = np.asarray(x, dtype=np.float32)
    out = np.zeros_like(x)
    mask = x > -10.0
    xv = x[mask]
    ln2 = np.float32(np.log(2.0))
    k = np.floor(xv / ln2).astype(np.int32)
    r = xv - k.astype(np.float32) * ln2
    er = np.float32(1.0) + r + r * r * np.float32(0.5) + r * r * r * np.float32(1.0 / 6.0)
    out[mask] = (er * np.power(np.float32(2.0), k.astype(np.float32))).astype(np.float32)
    return out


def poly_tanh(x: np.ndarray) -> np.ndarray:
    """Padé-3 tanh approximation; saturates at ±1 outside |x|>4.

    tanh(z) ≈ z*(27 + z²) / (27 + 9z²)  for |z|<=4.
    """
    x = np.asarray(x, dtype=np.float32)
    sign = np.sign(x)
    ax = np.abs(x)
    z2 = ax * ax
    pade = ax * (np.float32(27.0) + z2) / (np.float32(27.0) + np.float32(9.0) * z2)
    return np.where(ax > 4.0, sign, sign * pade).astype(np.float32)


def gelu_tanh(x: np.ndarray) -> np.ndarray:
    """Tanh approximation of GELU (matches PyTorch approximate='tanh')."""
    c = np.float32(np.sqrt(2.0 / np.pi))
    inner = c * (x + np.float32(0.044715) * x * x * x)
    return np.float32(0.5) * x * (np.float32(1.0) + poly_tanh(inner))


def softmax_causal(scores: np.ndarray) -> np.ndarray:
    """Softmax with causal mask along the last axis. scores shape: [..., T, T]."""
    T = scores.shape[-1]
    out = np.zeros_like(scores)
    for i in range(T):
        row = scores[..., i, : i + 1]
        m = np.max(row, axis=-1, keepdims=True)
        ex = poly_exp_neg(row - m)
        out[..., i, : i + 1] = ex / np.sum(ex, axis=-1, keepdims=True)
    return out


def layernorm(x: np.ndarray, gamma: np.ndarray, beta: np.ndarray) -> np.ndarray:
    mean = np.mean(x, axis=-1, keepdims=True).astype(np.float32)
    var = np.mean((x - mean) ** 2, axis=-1, keepdims=True).astype(np.float32)
    inv_std = np.float32(1.0) / np.sqrt(var + np.float32(1e-5))
    return ((x - mean) * inv_std * gamma + beta).astype(np.float32)


def to_array(t, shape) -> np.ndarray:
    return quantize_bf16(np.array(t, dtype=np.float32).reshape(shape))


def forward(weights: dict, cfg: dict, tokens: list[int]) -> np.ndarray:
    d_model = cfg["d_model"]
    n_heads = cfg["n_heads"]
    head_dim = d_model // n_heads
    n_layers = cfg["n_layers"]
    d_ff = cfg["d_ff"]
    vocab = cfg["vocab_size"]

    tok_emb = to_array(weights["tok_emb.weight"], (vocab, d_model))
    pos_emb = to_array(weights["pos_emb.weight"], (cfg["seq_len"], d_model))

    T = len(tokens)
    x = (tok_emb[tokens] + pos_emb[:T]).astype(np.float32)

    for layer in range(n_layers):
        p = f"blocks.{layer}."

        ln1_g = to_array(weights[p + "ln1.weight"], (d_model,))
        ln1_b = to_array(weights[p + "ln1.bias"], (d_model,))
        qkv_w = to_array(weights[p + "attn.qkv.weight"], (3 * d_model, d_model))
        out_w = to_array(weights[p + "attn.out.weight"], (d_model, d_model))
        ln2_g = to_array(weights[p + "ln2.weight"], (d_model,))
        ln2_b = to_array(weights[p + "ln2.bias"], (d_model,))
        up_w = to_array(weights[p + "ffn.up.weight"], (d_ff, d_model))
        down_w = to_array(weights[p + "ffn.down.weight"], (d_model, d_ff))

        # ---- Attention ----
        xn = layernorm(x, ln1_g, ln1_b)
        qkv = xn @ qkv_w.T  # [T, 3*d_model]
        q = qkv[:, :d_model].reshape(T, n_heads, head_dim).transpose(1, 0, 2)
        k = qkv[:, d_model : 2 * d_model].reshape(T, n_heads, head_dim).transpose(1, 0, 2)
        v = qkv[:, 2 * d_model :].reshape(T, n_heads, head_dim).transpose(1, 0, 2)

        scale = np.float32(1.0) / np.sqrt(np.float32(head_dim))
        scores = (q @ k.transpose(0, 2, 1)).astype(np.float32) * scale
        attn = softmax_causal(scores)  # [n_heads, T, T]
        head_out = attn @ v  # [n_heads, T, head_dim]
        attn_out = head_out.transpose(1, 0, 2).reshape(T, d_model)
        x = (x + attn_out @ out_w.T).astype(np.float32)

        # ---- FFN ----
        xn = layernorm(x, ln2_g, ln2_b)
        up = (xn @ up_w.T).astype(np.float32)
        h = gelu_tanh(up)
        x = (x + (h @ down_w.T)).astype(np.float32)

    ln_f_g = to_array(weights["ln_f.weight"], (d_model,))
    ln_f_b = to_array(weights["ln_f.bias"], (d_model,))
    head_w = to_array(weights["head.weight"], (vocab, d_model))

    x = layernorm(x, ln_f_g, ln_f_b)
    logits = (x @ head_w.T).astype(np.float32)
    return logits


def main() -> None:
    data = json.loads(TRANS8_WEIGHTS.read_text())
    cfg = data["config"]
    logits = forward(data["weights"], cfg, INPUT_TOKENS)
    preds = logits.argmax(-1)

    print("input :", " ".join(VOCAB_CHARS[t] for t in INPUT_TOKENS))
    print("preds :", " ".join(VOCAB_CHARS[t] for t in preds))
    print()
    print("Display string (9 chars expected on cells 0xE8..0xF0):")
    print("  '" + "".join(VOCAB_CHARS[t] for t in preds) + "'")


if __name__ == "__main__":
    main()
