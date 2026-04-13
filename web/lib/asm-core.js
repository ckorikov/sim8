/**
 * Shared operand helpers for the sim8 assembler.
 * Used by asm-fp.js, asm-vu.js, and asm.js.
 */

import {
    OpType,
    BY_MNEMONIC,
    GPR_CODES,
    ARITH_CODES,
    STACK_CODES,
    AsmError,
    TAG_REG,
    TAG_CONST,
    TAG_ADDR,
    TAG_REGADDR,
    TAG_FP_REG,
    TAG_FP_IMM,
    TAG_LABEL,
    TAG_ADDR_LABEL,
    TAG_PAGE_LABEL,
    encodeRegaddr,
} from "./asm-parse.js";

// ── Operand matching ─────────────────────────────────────────────

function _operandMatches(op, ot) {
    switch (ot) {
        case OpType.REG:
            return op.tag === TAG_REG;
        case OpType.REG_ARITH:
            return op.tag === TAG_REG && ARITH_CODES.has(op.code);
        case OpType.REG_GPR:
            return op.tag === TAG_REG && GPR_CODES.has(op.code);
        case OpType.REG_STACK:
            return op.tag === TAG_REG && STACK_CODES.has(op.code);
        case OpType.IMM:
            return op.tag === TAG_CONST || op.tag === TAG_LABEL || op.tag === TAG_PAGE_LABEL;
        case OpType.MEM:
            return op.tag === TAG_ADDR || op.tag === TAG_ADDR_LABEL;
        case OpType.REGADDR:
            return op.tag === TAG_REGADDR;
        case OpType.FP_REG:
            return op.tag === TAG_FP_REG;
        case OpType.FP_IMM8:
        case OpType.FP_IMM16:
            return op.tag === TAG_FP_IMM;
        default:
            return false;
    }
}

// ── Operand encoding ─────────────────────────────────────────────

export function _encodeOperand(op) {
    switch (op.tag) {
        case TAG_REG:
            return op.code;
        case TAG_CONST:
        case TAG_ADDR:
            return op.value;
        case TAG_REGADDR:
            return encodeRegaddr(op.regCode, op.offset);
        case TAG_LABEL:
        case TAG_ADDR_LABEL:
        case TAG_PAGE_LABEL:
            return 0; // placeholder for pass 2
        default:
            throw new Error(`unexpected operand: ${op.tag}`);
    }
}

// ── Instruction matching ─────────────────────────────────────────

export function _findInstr(mnemonic, operands, line, table = BY_MNEMONIC) {
    const candidates = table[mnemonic];
    if (!candidates) {
        throw new AsmError(`Invalid instruction: ${mnemonic}`, line);
    }

    for (const instr of candidates) {
        if (instr.format.length !== operands.length) continue;
        if (instr.format.every((ot, i) => _operandMatches(operands[i], ot))) return instr;
    }

    const maxArity = Math.max(...candidates.map((i) => i.format.length));
    if (operands.length > maxArity) {
        throw new AsmError(`${mnemonic}: too many arguments`, line);
    }
    throw new AsmError(`${mnemonic} does not support this operand(s)`, line);
}

// ── Suffix lookup ────────────────────────────────────────────────

/** Upper-case suffix → table lookup. Throws AsmError if not found. */
export function _lookupSuffix(suffix, table, errorDesc, line) {
    const upper = suffix.toUpperCase();
    if (!(upper in table)) throw new AsmError(`${errorDesc}: .${suffix}`, line);
    return table[upper];
}
