/**
 * Shared state hub for all UI modules.
 * Single source of truth for CPU instance, assembly results, theme colors, and utilities.
 */

import { CPU, IO_START, SP_INIT, PAGE_SIZE } from '../lib/core.js';

// ── CPU instance ────────────────────────────────────────────────

export const cpu = new CPU();

// ── Constants ───────────────────────────────────────────────────

export const STACK_BASE = SP_INIT - 2;
export const IO_BASE = IO_START;
export { PAGE_SIZE };

// ── Assembly state (mutated by orchestrator) ────────────────────

export const asm = {
  labels: {},         // label name → address
  mapping: {},        // address → source line (1-based)
  instrStarts: new Set(),
  codeLen: 0,
};

// ── CSS helper ──────────────────────────────────────────────────

export function cssVar(name) {
  return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
}

// ── Theme colors (mutated in-place on theme switch) ─────────────

export const colors = {};
export const regColors = {};

export function refreshColors() {
  Object.assign(colors, {
    or: cssVar('--a-orange'), bl: cssVar('--a-blue'),
    gr: cssVar('--a-green'), rd: cssVar('--a-red'),
    yl: cssVar('--a-yellow'), dim: cssVar('--t-dim'),
    mid: cssVar('--t-mid'), txt: cssVar('--t-text'),
  });
  Object.assign(regColors, {
    A: colors.gr, B: colors.bl, C: colors.or, D: colors.rd,
    IP: colors.or, SP: colors.yl, DP: colors.mid,
  });
}
refreshColors();

// ── Formatting utilities ────────────────────────────────────────

export function hex(v, p = 2) {
  return v.toString(16).toUpperCase().padStart(p, '0');
}

export function printableChar(v) {
  return (v >= 32 && v < 127) ? String.fromCharCode(v) : '';
}
