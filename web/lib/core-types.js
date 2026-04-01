/**
 * CPU building blocks: Memory, ALU, Flags, FPU registers, RegisterFile, decoder.
 * Extracted from core.js for modularity.
 */

import {
    BY_CODE,
    BY_CODE_FP,
    BY_CODE_VU,
    FP_FMT_WIDTH,
    Op,
    Reg,
    ISA,
    ISA_FP,
    ISA_VU,
    decodeRegaddr,
    decodeFpm,
    validateFpm,
    FP_FMT_H,
    FP_FMT_BF,
    FP_FMT_O3,
    FP_FMT_O2,
    VU_ASYNC_OPS,
    VU_ARITH_OPS,
    VU_UNARY_OPS,
    VU_VV_ONLY_OPS,
    VU_INT_FMTS,
    VU_FMT_ELEM_SIZE,
    VU_FMT_U,
    VU_FMT_I,
    VU_MODE_VV,
    VU_MODE_VS,
    VU_MODE_VI,
    VU_MODE_R,
    VU_WINDOW_SIZE,
    VU_CMP_EQ,
    VU_CMP_NE,
    VU_CMP_LT,
    VU_CMP_LE,
    VU_CMP_GT,
    VU_CMP_GE,
    decodeVfm,
    decodeVuRegs,
} from "./isa.js";

// Re-export ISA symbols used by core.js (avoids redundant core.js → isa.js edge)
export {
    Op,
    Reg,
    ISA,
    ISA_FP,
    ISA_VU,
    decodeRegaddr,
    decodeFpm,
    validateFpm,
    FP_FMT_WIDTH,
    FP_FMT_H,
    FP_FMT_BF,
    FP_FMT_O3,
    FP_FMT_O2,
    VU_ASYNC_OPS,
    VU_ARITH_OPS,
    VU_UNARY_OPS,
    VU_VV_ONLY_OPS,
    VU_INT_FMTS,
    VU_FMT_ELEM_SIZE,
    VU_FMT_U,
    VU_FMT_I,
    VU_MODE_VV,
    VU_MODE_VS,
    VU_MODE_VI,
    VU_MODE_R,
    VU_WINDOW_SIZE,
    VU_CMP_EQ,
    VU_CMP_NE,
    VU_CMP_LT,
    VU_CMP_LE,
    VU_CMP_GT,
    VU_CMP_GE,
    decodeVfm,
    decodeVuRegs,
};

// ── Constants ────────────────────────────────────────────────────

const MEMORY_SIZE = 65536;
export const PAGE_SIZE = 256;
export const IO_START = 232;
export const SP_INIT = 231;

export const CpuState = Object.freeze({
    IDLE: "IDLE",
    RUNNING: "RUNNING",
    HALTED: "HALTED",
    FAULT: "FAULT",
});

export const ErrorCode = Object.freeze({
    DIV_ZERO: 1,
    STACK_OVERFLOW: 2,
    STACK_UNDERFLOW: 3,
    INVALID_REG: 4,
    PAGE_BOUNDARY: 5,
    INVALID_OPCODE: 6,
    FP_FORMAT: 12,
    VU_OOB: 13,
    VU_FORMAT: 14,
});

// ── CpuFault ─────────────────────────────────────────────────────

export class CpuFault extends Error {
    constructor(code, ip = 0) {
        super(`FAULT(${code}) at IP=${ip}`);
        this.code = code;
        this.ip = ip;
    }
}

// ── Memory ───────────────────────────────────────────────────────

export class Memory {
    constructor() {
        this._data = new Uint8Array(MEMORY_SIZE);
        this._nonZero = 0; // tracked incrementally for usedBytes()
    }

    get(addr) {
        return this._data[addr];
    }

    /** @returns {boolean} true if addr is in the I/O region (excluded from usedBytes) */
    _isIO(addr) {
        return addr < PAGE_SIZE && addr >= IO_START;
    }

    set(addr, val) {
        const byte = val & 0xff;
        const old = this._data[addr];
        this._data[addr] = byte;
        if (!this._isIO(addr)) {
            if (old === 0 && byte !== 0) this._nonZero++;
            else if (old !== 0 && byte === 0) this._nonZero--;
        }
    }

    load(data, offset = 0) {
        if (offset + data.length > MEMORY_SIZE) {
            throw new RangeError(
                `Data (${data.length} bytes at offset ${offset}) exceeds memory size (${MEMORY_SIZE})`,
            );
        }
        for (let i = 0; i < data.length; i++) {
            this.set(offset + i, data[i]);
        }
    }

    reset() {
        this._data.fill(0);
        this._nonZero = 0;
    }

    usedBytes() {
        return this._nonZero;
    }
}

// ── ALU ──────────────────────────────────────────────────────────

export const ALU = {
    add(a, b) {
        const raw = a + b;
        const carry = raw > 255;
        const result = raw & 0xff;
        return [result, carry, result === 0];
    },

    sub(a, b) {
        const raw = a - b;
        const carry = raw < 0;
        const result = ((raw % 256) + 256) % 256;
        return [result, carry, result === 0];
    },

    mul(a, b) {
        const raw = a * b;
        const carry = raw > 255;
        const result = raw & 0xff;
        return [result, carry, result === 0];
    },

    div(a, b) {
        const result = Math.floor(a / b);
        const carry = result > 255 || result < 0;
        const clamped = ((result % 256) + 256) % 256;
        return [clamped, carry, clamped === 0];
    },

    inc(a) {
        const raw = a + 1;
        const carry = raw > 255;
        const result = raw & 0xff;
        return [result, carry, result === 0];
    },

    dec(a) {
        const raw = a - 1;
        const carry = raw < 0;
        const result = ((raw % 256) + 256) % 256;
        return [result, carry, result === 0];
    },

    and_op(a, b) {
        const result = a & b;
        return [result, result === 0];
    },

    or_op(a, b) {
        const result = a | b;
        return [result, result === 0];
    },

    xor_op(a, b) {
        const result = a ^ b;
        return [result, result === 0];
    },

    not_op(a) {
        const result = a ^ 0xff;
        return [result, result === 0];
    },

    shl(value, count) {
        if (count >= 8) return [0, value !== 0, true];
        const raw = (value << count) & 0xffff;
        const carry = raw > 255;
        const result = raw & 0xff;
        return [result, carry, result === 0];
    },

    shr(value, count) {
        if (count >= 8) return [0, value !== 0, true];
        const carry = (value & ((1 << count) - 1)) !== 0;
        const result = value >>> count;
        return [result, carry, result === 0];
    },
};

// ── Flags ────────────────────────────────────────────────────────

class Flags {
    constructor() {
        this.z = false;
        this.c = false;
        this.f = false;
    }

    reset() {
        this.z = false;
        this.c = false;
        this.f = false;
    }
}

// ── FpuRegisters ─────────────────────────────────────────────────

// Shared buffer for raw-bits <-> float32 conversion inside FpuRegisters
const _fpBuf = new ArrayBuffer(4);
const _fpF32 = new Float32Array(_fpBuf);
const _fpU32 = new Uint32Array(_fpBuf);

class FpuRegisters {
    constructor() {
        this._fp32 = [0, 0];
        this.fpcr = 0;
        this.fpsr = 0;
    }

    get fa() {
        _fpU32[0] = this._fp32[0] >>> 0;
        return _fpF32[0];
    }
    get fb() {
        _fpU32[0] = this._fp32[1] >>> 0;
        return _fpF32[0];
    }

    get roundingMode() {
        return this.fpcr & 0x03;
    }

    readBits(pos, fmt, phys = 0) {
        const width = FP_FMT_WIDTH[fmt];
        if (width === 32) {
            return this._fp32[phys] >>> 0;
        }
        const bitOffset = pos * width;
        const mask = (1 << width) - 1;
        return (this._fp32[phys] >> bitOffset) & mask;
    }

    writeBits(pos, fmt, value, phys = 0) {
        const width = FP_FMT_WIDTH[fmt];
        if (width === 32) {
            this._fp32[phys] = value >>> 0;
            return;
        }
        const bitOffset = pos * width;
        const mask = (1 << width) - 1;
        this._fp32[phys] = ((this._fp32[phys] & ~(mask << bitOffset)) | ((value & mask) << bitOffset)) >>> 0;
    }

    accumulateExceptions(exc) {
        if (exc.invalid) this.fpsr |= 0x01;
        if (exc.divZero) this.fpsr |= 0x02;
        if (exc.overflow) this.fpsr |= 0x04;
        if (exc.underflow) this.fpsr |= 0x08;
        if (exc.inexact) this.fpsr |= 0x10;
    }

    reset() {
        this._fp32[0] = 0;
        this._fp32[1] = 0;
        this.fpcr = 0;
        this.fpsr = 0;
    }
}

// ── RegisterFile ─────────────────────────────────────────────────

export class RegisterFile {
    constructor(arch = 1) {
        this._regs = [0, 0, 0, 0, SP_INIT, 0];
        this.ip = 0;
        this.flags = new Flags();
        this.fpu = arch >= 2 ? new FpuRegisters() : null;
    }

    read(code) {
        return this._regs[code];
    }
    write(code, val) {
        this._regs[code] = val & 0xff;
    }

    get a() {
        return this._regs[0];
    }
    set a(val) {
        this._regs[0] = val & 0xff;
    }

    get b() {
        return this._regs[1];
    }
    set b(val) {
        this._regs[1] = val & 0xff;
    }

    get c() {
        return this._regs[2];
    }
    set c(val) {
        this._regs[2] = val & 0xff;
    }

    get d() {
        return this._regs[3];
    }
    set d(val) {
        this._regs[3] = val & 0xff;
    }

    get sp() {
        return this._regs[4];
    }
    set sp(val) {
        this._regs[4] = val & 0xff;
    }

    get dp() {
        return this._regs[5];
    }
    set dp(val) {
        this._regs[5] = val & 0xff;
    }

    reset(arch = 1) {
        this._regs = [0, 0, 0, 0, SP_INIT, 0];
        this.ip = 0;
        this.flags.reset();
        if (arch >= 2) {
            if (this.fpu === null) {
                this.fpu = new FpuRegisters();
            } else {
                this.fpu.reset();
            }
        } else {
            this.fpu = null;
        }
    }
}

// ── Decoder ──────────────────────────────────────────────────────

export function decode(mem, ip, arch) {
    const opcode = mem.get(ip);
    let defn = BY_CODE[opcode];
    if (defn === undefined && arch >= 2) {
        defn = BY_CODE_FP[opcode];
    }
    if (defn === undefined && arch >= 3) {
        defn = BY_CODE_VU[opcode];
    }
    if (defn === undefined) {
        throw new CpuFault(ErrorCode.INVALID_OPCODE, ip);
    }
    let size = defn.size;
    // VU async instructions have variable size depending on VFM mode
    if (defn.formatDep && arch >= 3 && ip + 1 < PAGE_SIZE) {
        const vfm = mem.get(ip + 1);
        const mode = (vfm >> 3) & 3;
        if (mode === VU_MODE_VI) {
            const fmt = vfm & 7;
            const elemSize = VU_FMT_ELEM_SIZE[fmt] || 1;
            size = 3 + elemSize;
        }
    }
    if (ip + size > PAGE_SIZE) {
        throw new CpuFault(ErrorCode.PAGE_BOUNDARY, ip);
    }
    const operands = [];
    for (let k = 1; k < size; k++) {
        operands.push(mem.get(ip + k));
    }
    return { op: defn.op, size, operands };
}

// ── Byte conversion helpers ──────────────────────────────────────

export function intFromBytesLE(data) {
    let raw = 0;
    for (let i = data.length - 1; i >= 0; i--) {
        raw = (raw << 8) | data[i];
    }
    if (data.length === 4) return raw >>> 0;
    return raw;
}

export function intToBytesLE(raw, nbytes) {
    const data = new Uint8Array(nbytes);
    for (let i = 0; i < nbytes; i++) {
        data[i] = (raw >> (i * 8)) & 0xff;
    }
    return data;
}
