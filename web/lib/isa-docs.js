/**
 * Human-readable documentation for ISA elements.
 *
 * Single source of truth used by:
 *   - web/src/editor.js  (CodeMirror autocomplete/hover)
 *   - vscode-sim8        (VS Code hover provider, via esbuild bundle)
 */

import {
    OpType,
    FP_REGISTERS,
    FP_FMT_F,
    FP_FMT_H,
    FP_FMT_BF,
    FP_FMT_O3,
    FP_FMT_O2,
    FP_FMT_N1,
    FP_FMT_N2,
} from "./isa.js";

// ── One-line descriptions ─────────────────────────────────────────────────────

export const MNEMONIC_INFO = Object.freeze({
    HLT: "Halt CPU execution",
    MOV: "Copy value: reg, mem, or immediate",
    ADD: "dest = dest + src; sets C, Z",
    SUB: "dest = dest - src; sets C, Z",
    INC: "dest = dest + 1; sets C, Z",
    DEC: "dest = dest - 1; sets C, Z",
    CMP: "dest - src (no store); Z=1 if equal, C=1 if src > dest",
    MUL: "A = A * src; sets C, Z",
    DIV: "A = A / src (integer); FAULT if src=0",
    AND: "dest = dest & src; C=0, sets Z",
    OR: "dest = dest | src; C=0, sets Z",
    XOR: "dest = dest ^ src; C=0, sets Z",
    NOT: "dest = ~dest; C=0, sets Z",
    SHL: "dest = dest << n; sets C if overflow",
    SHR: "dest = dest >>> n; sets C if bits lost",
    JMP: "Unconditional jump",
    JC: "Jump if C=1 (carry); after CMP: <",
    JNC: "Jump if C=0 (no carry); after CMP: >=",
    JZ: "Jump if Z=1 (zero); after CMP: ==",
    JNZ: "Jump if Z=0 (not zero); after CMP: !=",
    JA: "Jump if C=0 and Z=0 (above); after CMP: >",
    JNA: "Jump if C=1 or Z=1 (not above); after CMP: <=",
    PUSH: "Push to stack; SP--; FAULT if SP=0",
    POP: "Pop from stack; SP++; FAULT if SP>=231",
    CALL: "Push return addr, jump to target",
    RET: "Pop addr from stack, jump to it",
    DB: "Define raw byte(s), string, or FP data",
    FMOV: "FP load/store or register copy",
    FADD: "FP dst = dst + src",
    FSUB: "FP dst = dst - src",
    FMUL: "FP dst = dst * src",
    FDIV: "FP dst = dst / src",
    FCMP: "FP compare; sets Z, C (Z=C=1 if NaN)",
    FABS: "Clear sign bit of FP register",
    FNEG: "Toggle sign bit of FP register",
    FSQRT: "FP square root",
    FCVT: "Convert between FP formats",
    FITOF: "uint8 GPR to FP register",
    FFTOI: "FP to uint8 GPR (saturating)",
    FSTAT: "Read FPSR (exception flags) to GPR",
    FCFG: "Read FPCR (rounding mode) to GPR",
    FSCFG: "Write GPR to FPCR (bits [1:0] only)",
    FCLR: "Clear all FPSR sticky flags",
    FCLASS: "Classify FP value to 8-bit bitmask",
    FMADD: "FP dst = src * mem + dst (fused)",
    VSET: "Set VU register (VA/VB/VC/VM/VL) from imm16, GPR pair, single GPR, or memory",
    VFSTAT: "Read VFPSR (vector FP exception flags) to GPR",
    VFCLR: "Clear all VFPSR sticky flags",
    VWAIT: "Wait for VU queue to drain; propagate VU faults to CPU",
    VADD: "Vector dst = src1 + src2 (element-wise)",
    VSUB: "Vector dst = src1 - src2 (element-wise)",
    VMUL: "Vector dst = src1 * src2 (element-wise)",
    VDIV: "Vector dst = src1 / src2 (element-wise)",
    VMAX: "Vector dst = max(src1, src2) (element-wise)",
    VMIN: "Vector dst = min(src1, src2) (element-wise)",
    VDOT: "Vector dot product: dst += sum(src1 * src2)",
    VSQRT: "Vector dst = sqrt(src1) (element-wise)",
    VNEG: "Vector dst = -src1 (element-wise)",
    VABS: "Vector dst = |src1| (element-wise)",
    VCMP: "Vector compare → byte mask at [VM]",
    VSEL: "Vector select: dst[i] = mask[i] ? dst[i] : alt[i]",
    VMOV: "Vector memory copy or broadcast fill (vi mode / VFILL alias)",
});

// ── Integer flag effects ──────────────────────────────────────────────────────
// Mnemonics absent from this map do not affect flags.

export const MNEMONIC_FLAGS = Object.freeze({
    ADD: "Z (result=0), C (unsigned overflow)",
    SUB: "Z (result=0), C (borrow)",
    INC: "Z (result=0), C (was 255)",
    DEC: "Z (result=0), C (was 0)",
    CMP: "Z=1 if equal; C=1 if a < b (unsigned)",
    MUL: "Z (result=0), C (overflow)",
    DIV: "Z (result=0), C=0",
    AND: "Z (result=0), C=0",
    OR: "Z (result=0), C=0",
    XOR: "Z (result=0), C=0",
    NOT: "Z (result=0), C=0",
    SHL: "Z (result=0), C (last bit shifted out)",
    SHR: "Z (result=0), C (last bit shifted out)",
    FCMP: "Z, C (integer flags; Z=C=1 if unordered/NaN)",
});

// ── FP exception flags ───────────────────────────────────────────────────────
// Mnemonics absent from this map raise no FP exceptions.

export const MNEMONIC_FP_EXCEPTIONS = Object.freeze({
    FADD: "NV, OF, UF, NX",
    FSUB: "NV, OF, UF, NX",
    FMUL: "NV (0×Inf), OF, UF, NX",
    FDIV: "NV (0/0, Inf/Inf), DZ (x/0), OF, UF, NX",
    FCMP: "NV (sNaN)",
    FSQRT: "NV (sqrt of negative or sNaN), NX",
    FCVT: "NV (sNaN), OF, UF, NX",
    FITOF: "NX",
    FFTOI: "NV (NaN, ±Inf), NX",
    FMADD: "NV, DZ, OF, UF, NX",
});

// ── Special notes ─────────────────────────────────────────────────────────────

export const MNEMONIC_NOTES = Object.freeze({
    DIV: "FAULT if divisor is zero (ERR_DIV_ZERO).",
    PUSH: "FAULT if SP=0 (ERR_STACK_OVERFLOW).",
    POP: "FAULT if SP≥231 (ERR_STACK_UNDERFLOW).",
    JMP: "Target must be on page 0.",
    CALL: "Target must be on page 0.",
    FCVT: "Identical src/dst format is rejected — use FMOV instead.",
    FSTAT: "FPSR bits: [0]=NV, [1]=DZ, [2]=OF, [3]=UF, [4]=NX.",
    FCFG: "FPCR bits [1:0]: 00=RNE, 01=RTZ, 10=RDN, 11=RUP.",
    FSCFG: "Only bits [1:0] are writable; reserved bits [7:2] are cleared.",
    VDOT: "FP-only (no .U/.I). dst gets scalar result (elem_size bytes).",
});

// ── Syntax form overrides (when ISA table signatures aren't descriptive enough) ─

export const MNEMONIC_FORMS_OVERRIDE = Object.freeze({
    VSET: [
        "VSET ptr, imm16",
        "VSET ptr, {label}, label",
        "VSET ptr, rH, rL",
        "VSET ptr, gpr",
        "VSET ptr, [addr]",
        "VSET ptr, [reg±offset]",
    ],
});

// ── Operand type → human-readable label ──────────────────────────────────────

export const SIG_LABELS = Object.freeze({
    [OpType.REG]: "reg",
    [OpType.REG_ARITH]: "reg|SP",
    [OpType.REG_STACK]: "gpr|DP",
    [OpType.REG_GPR]: "gpr",
    [OpType.IMM]: "imm",
    [OpType.MEM]: "[addr]",
    [OpType.REGADDR]: "[reg±off]",
    [OpType.FP_REG]: "fp",
    [OpType.FP_IMM8]: "imm8",
    [OpType.FP_IMM16]: "imm16",
});

// ── FP format code → short name ───────────────────────────────────────────────

export const FP_FMT_NAMES = Object.freeze({
    [FP_FMT_F]: "float32",
    [FP_FMT_H]: "float16",
    [FP_FMT_BF]: "bfloat16",
    [FP_FMT_O3]: "ofp8-e4m3",
    [FP_FMT_O2]: "ofp8-e5m2",
    [FP_FMT_N1]: "nf4-e2m1",
    [FP_FMT_N2]: "nf4-e1m2",
});

// ── FP suffix string → format details ────────────────────────────────────────
// Keys match FP_SUFFIX_TO_FMT from isa.js (no leading dot).

export const FP_FORMAT_DOCS = Object.freeze({
    F: { exmy: "E8M23", name: "float32", bits: 32, registers: "FA, FB" },
    E8M23: { exmy: "E8M23", name: "float32", bits: 32, registers: "FA, FB" },
    H: { exmy: "E5M10", name: "float16", bits: 16, registers: "FHA–FHD" },
    E5M10: { exmy: "E5M10", name: "float16", bits: 16, registers: "FHA–FHD" },
    BF: { exmy: "E8M7", name: "bfloat16", bits: 16, registers: "FHA–FHD" },
    E8M7: { exmy: "E8M7", name: "bfloat16", bits: 16, registers: "FHA–FHD" },
    O3: { exmy: "E4M3", name: "OFP8 E4M3", bits: 8, registers: "FQA–FQH", note: "No ±Inf, max=448" },
    E4M3: { exmy: "E4M3", name: "OFP8 E4M3", bits: 8, registers: "FQA–FQH", note: "No ±Inf, max=448" },
    O2: { exmy: "E5M2", name: "OFP8 E5M2", bits: 8, registers: "FQA–FQH" },
    E5M2: { exmy: "E5M2", name: "OFP8 E5M2", bits: 8, registers: "FQA–FQH" },
    N1: { exmy: "E2M1", name: "4-bit", bits: 4, registers: "FOA–FOP", note: "Reserved — triggers ERR_FP_FORMAT" },
    E2M1: { exmy: "E2M1", name: "4-bit", bits: 4, registers: "FOA–FOP", note: "Reserved — triggers ERR_FP_FORMAT" },
    N2: { exmy: "E1M2", name: "4-bit", bits: 4, registers: "FOA–FOP", note: "Reserved — triggers ERR_FP_FORMAT" },
    E1M2: { exmy: "E1M2", name: "4-bit", bits: 4, registers: "FOA–FOP", note: "Reserved — triggers ERR_FP_FORMAT" },
});

// ── Register documentation ────────────────────────────────────────────────────

export const REGISTER_DOCS = Object.freeze({
    A: { type: "GPR", description: "8-bit GPR. Implicit destination for MUL/DIV." },
    B: { type: "GPR", description: "8-bit GPR." },
    C: { type: "GPR", description: "8-bit GPR." },
    D: { type: "GPR", description: "8-bit GPR." },
    SP: {
        type: "Special",
        description: "Stack Pointer. Auto-decrements on PUSH, auto-increments on POP. Stack is always on page 0.",
    },
    DP: {
        type: "Special",
        description: "Data Page register. Selects memory page (0–255) for [addr] and [reg±offset] accesses.",
    },
    ...Object.fromEntries(
        Object.entries(FP_REGISTERS).map(([name, { fmt, width }]) => [
            name,
            { type: `FP-${width}`, description: `${width}-bit FP register (${FP_FMT_NAMES[fmt] ?? `${width}b`}).` },
        ]),
    ),
});

// ── Directive documentation ───────────────────────────────────────────────────

export const DIRECTIVE_DOCS = Object.freeze({
    "@PAGE": {
        description: "Switch output to page N (0–255), optionally at byte offset M.",
        syntax: ["@page N", "@page N, M"],
        note: "JMP/CALL targets must be on page 0. Gaps between sections are zero-filled.",
    },
    "@INCLUDE": {
        description: "Include another source file at this point.",
        syntax: ['@include "path/to/file.asm"', '@include "https://..."'],
        note: "Max include depth: 16. Circular includes are detected.",
    },
    DB: {
        description: "Define raw byte(s), a string, or floating-point data.",
        syntax: ["DB imm8 [, imm8, ...]", 'DB "string"', "DB 1.5_f, 2.0_h, ..."],
        note: "Float suffixes: `_f` (float32), `_h` (float16), `_bf` (bfloat16), `_o3` (OFP8 E4M3), `_o2` (OFP8 E5M2).",
    },
});
