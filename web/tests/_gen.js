/**
 * Random valid assembly program generator for cross-validation testing.
 * Uses ISA tables to produce programs that assemble and terminate.
 */

import { ISA, ISA_FP, OpType, FP_CONTROL_MNEMONICS } from "../lib/isa.js";

// ── Seeded PRNG (xorshift32) ────────────────────────────────────────

function mkRng(seed) {
    let s = seed | 1;
    return {
        next() {
            s ^= s << 13;
            s ^= s >> 17;
            s ^= s << 5;
            return (s >>> 0) / 0x100000000;
        },
        int(lo, hi) {
            return lo + Math.floor(this.next() * (hi - lo + 1));
        },
        pick(arr) {
            return arr[this.int(0, arr.length - 1)];
        },
    };
}

// ── Constants ───────────────────────────────────────────────────────

const GPR_NAMES = ["A", "B", "C", "D"];
const ARITH_NAMES = ["A", "B", "C", "D", "SP"];
const STACK_NAMES = ["A", "B", "C", "D", "DP"];
const FP_SUFFIXES = ["F", "H", "BF", "O3", "O2"];
const FP_REG_BY_SUFFIX = {
    F: ["FA", "FB"],
    H: ["FHA", "FHB", "FHC", "FHD"],
    BF: ["FHA", "FHB", "FHC", "FHD"],
    O3: ["FQA", "FQB", "FQC", "FQD", "FQE", "FQF", "FQG", "FQH"],
    O2: ["FQA", "FQB", "FQC", "FQD", "FQE", "FQF", "FQG", "FQH"],
};

// Safe memory addresses (above code region, below stack/IO)
const SAFE_ADDR_LO = 80;
const SAFE_ADDR_HI = 200;

// Edge-case immediate values
const EDGE_IMMS = [0, 1, 2, 7, 8, 15, 31, 32, 127, 128, 170, 255];

// Instructions to skip in generation (control flow makes termination hard)
const SKIP_MNEMONICS = new Set([
    "JMP",
    "JC",
    "JNC",
    "JZ",
    "JNZ",
    "JA",
    "JNA",
    "CALL",
    "RET",
    "DB",
    "FCVT", // requires dual suffix (complex)
    "FMADD", // 3 operands with memory (complex)
]);

// ── Operand generation ──────────────────────────────────────────────

function genOperand(rng, opType, fpSuffix) {
    switch (opType) {
        case OpType.REG:
            return rng.pick(ARITH_NAMES);
        case OpType.REG_GPR:
            return rng.pick(GPR_NAMES);
        case OpType.REG_ARITH:
            return rng.pick(ARITH_NAMES);
        case OpType.REG_STACK:
            return rng.pick(STACK_NAMES);
        case OpType.IMM:
            return String(rng.pick(EDGE_IMMS));
        case OpType.MEM:
            return `[${rng.int(SAFE_ADDR_LO, SAFE_ADDR_HI)}]`;
        case OpType.REGADDR: {
            const reg = rng.pick(GPR_NAMES);
            const off = rng.int(-16, 15);
            return off === 0 ? `[${reg}]` : `[${reg}${off > 0 ? "+" : ""}${off}]`;
        }
        case OpType.FP_REG:
            return rng.pick(FP_REG_BY_SUFFIX[fpSuffix] || ["FA"]);
        case OpType.FP_IMM8:
        case OpType.FP_IMM16:
            // FP immediates have complex encoding rules — skip these instruction forms
            return null;
        default:
            return "0";
    }
}

// ── Program generation ──────────────────────────────────────────────

/**
 * Generate a valid assembly program from a seed.
 * @param {number} seed - deterministic RNG seed
 * @param {{ maxInstrs?: number, arch?: number, useFP?: boolean }} opts
 * @returns {string} assembly source
 */
export function generateProgram(seed, { maxInstrs = 10, useFP = false } = {}) {
    const rng = mkRng(seed);
    const lines = [];
    let pushCount = 0;

    // Setup: put safe values in registers for regaddr to work
    lines.push(`MOV A, ${rng.int(SAFE_ADDR_LO, SAFE_ADDR_HI)}`);
    lines.push(`MOV B, ${rng.int(SAFE_ADDR_LO, SAFE_ADDR_HI)}`);
    lines.push(`MOV C, ${rng.int(0, 255)}`);
    lines.push(`MOV D, ${rng.int(0, 255)}`);

    // Collect candidate instructions
    const intCandidates = ISA.filter((d) => !SKIP_MNEMONICS.has(d.mnemonic));
    const fpCandidates = ISA_FP.filter((d) => !SKIP_MNEMONICS.has(d.mnemonic));

    const nInstrs = rng.int(3, maxInstrs);
    for (let i = 0; i < nInstrs; i++) {
        const pool = useFP && rng.next() > 0.5 ? fpCandidates : intCandidates;
        if (pool.length === 0) continue;

        const def = rng.pick(pool);
        const mnemonic = def.mnemonic;

        // Skip PUSH if we've pushed too many (avoid stack overflow)
        if (mnemonic === "PUSH" && pushCount >= 15) continue;
        // Skip POP if nothing pushed
        if (mnemonic === "POP" && pushCount <= 0) continue;
        // Skip DIV — might divide by zero and fault, complicating comparison
        if (mnemonic === "DIV") continue;

        if (mnemonic === "PUSH") pushCount++;
        if (mnemonic === "POP") pushCount--;

        // Determine FP suffix if needed
        let suffix = "";
        const isFP = FP_CONTROL_MNEMONICS.has(mnemonic) ? false : def.format.some((s) => s === OpType.FP_REG);
        if (isFP) {
            suffix = "." + rng.pick(FP_SUFFIXES);
        }

        // Generate operands
        const fpSuffix = suffix.slice(1) || "F";
        const operands = def.format.map((s) => genOperand(rng, s, fpSuffix));

        // Skip if any operand generation failed (e.g. FP_IMM)
        if (operands.some((o) => o === null)) continue;

        lines.push(`${mnemonic}${suffix} ${operands.join(", ")}`.trim());
    }

    // Balance stack
    while (pushCount > 0) {
        lines.push("POP A");
        pushCount--;
    }

    lines.push("HLT");
    return lines.join("\n");
}
