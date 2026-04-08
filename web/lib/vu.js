/**
 * Vector Unit state: registers, command queue, and execution engine.
 * Pure logic -- no DOM dependencies.
 */

import { bytesToFloat, floatToBytes, fpAdd, fpSub, fpMul, fpDiv, fpSqrt } from "./fp.js";

import {
    Op,
    VU_FMT_ELEM_SIZE,
    VU_FMT_U,
    VU_FMT_I,
    VU_MODE_VV,
    VU_MODE_R,
    VU_WINDOW_SIZE,
    VU_CMP_EQ,
    VU_CMP_NE,
    VU_CMP_LT,
    VU_CMP_LE,
    VU_CMP_GT,
    VU_CMP_GE,
    VU_ARITH_OPS,
    VU_UNARY_OPS,
    ErrorCode,
} from "./core-types.js";

export const VU_QUEUE_DEPTH = 4;

const MEMORY_SIZE = 65536;

const VuState = Object.freeze({
    IDLE: "IDLE",
    BUSY: "BUSY",
});

const _FP_FMTS = new Set([0, 1, 2, 3, 4]); // F, H, BF, O3, O2
const _FMT_NAMES = ["F", "H", "BF", "O3", "O2", "U", "I"];
const _hex16 = (v) => v.toString(16).toUpperCase().padStart(4, "0");

// ── Exception accumulation ───────────────────────────────────────

function _excToFlags(exc) {
    let flags = 0;
    if (exc.invalid) flags |= 0x01;
    if (exc.divZero) flags |= 0x02;
    if (exc.overflow) flags |= 0x04;
    if (exc.underflow) flags |= 0x08;
    if (exc.inexact) flags |= 0x10;
    return flags;
}

const _NO_EXC = Object.freeze({
    invalid: false,
    divZero: false,
    overflow: false,
    underflow: false,
    inexact: false,
});

// ── Element memory I/O ──────────────────────────────────────────

function _readElem(mem, addr, fmt) {
    const sz = VU_FMT_ELEM_SIZE[fmt];
    if (_FP_FMTS.has(fmt)) {
        const data = new Uint8Array(sz);
        for (let i = 0; i < sz; i++) data[i] = mem.get(addr + i);
        return bytesToFloat(data, fmt);
    }
    const val = mem.get(addr);
    if (fmt === VU_FMT_I) {
        return val < 128 ? val : val - 256;
    }
    return val;
}

function _writeElem(mem, addr, fmt, val, rm) {
    const sz = VU_FMT_ELEM_SIZE[fmt];
    if (_FP_FMTS.has(fmt)) {
        const { data, exc } = floatToBytes(Number(val), fmt, rm);
        for (let i = 0; i < sz; i++) mem.set(addr + i, data[i]);
        return exc;
    }
    mem.set(addr, val & 0xff);
    return _NO_EXC;
}

// ── Element arithmetic ──────────────────────────────────────────

function _arithFp(op, a, b, fmt, rm) {
    if (op === Op.VADD) return fpAdd(a, b, fmt, rm);
    if (op === Op.VSUB) return fpSub(a, b, fmt, rm);
    if (op === Op.VMUL) return fpMul(a, b, fmt, rm);
    if (op === Op.VDIV) return fpDiv(a, b, fmt, rm);
    if (op === Op.VMAX) {
        const val = Number.isNaN(a) ? b : Number.isNaN(b) ? a : Math.max(a, b);
        return { result: val, exc: _NO_EXC };
    }
    if (op === Op.VMIN) {
        const val = Number.isNaN(a) ? b : Number.isNaN(b) ? a : Math.min(a, b);
        return { result: val, exc: _NO_EXC };
    }
    throw new Error(`Unknown FP VU op: ${op}`);
}

function _intExc(raw) {
    return { invalid: false, divZero: false, overflow: raw > 255, underflow: raw < 0, inexact: false };
}

function _arithUint8(op, a, b) {
    const ua = a & 0xff;
    const ub = b & 0xff;
    if (op === Op.VADD) {
        const r = ua + ub;
        return { result: r & 0xff, exc: _intExc(r) };
    }
    if (op === Op.VSUB) {
        const r = ua - ub;
        return { result: ((r % 256) + 256) % 256, exc: _intExc(r) };
    }
    if (op === Op.VMUL) {
        const r = ua * ub;
        return { result: r & 0xff, exc: _intExc(r) };
    }
    if (op === Op.VDIV) return { result: ub === 0 ? 0 : Math.floor(ua / ub), exc: _NO_EXC };
    if (op === Op.VMAX) return { result: Math.max(ua, ub), exc: _NO_EXC };
    if (op === Op.VMIN) return { result: Math.min(ua, ub), exc: _NO_EXC };
    throw new Error(`Unknown UINT8 VU op: ${op}`);
}

function _arithInt8(op, a, b) {
    if (op === Op.VADD) {
        const r = a + b;
        return { result: r & 0xff, exc: _intExc(r) };
    }
    if (op === Op.VSUB) {
        const r = a - b;
        return { result: ((r % 256) + 256) % 256, exc: _intExc(r) };
    }
    if (op === Op.VMUL) {
        const r = a * b;
        return { result: r & 0xff, exc: _intExc(r) };
    }
    if (op === Op.VDIV) {
        if (b === 0) return { result: 0, exc: _NO_EXC };
        const sign = a < 0 !== b < 0 ? -1 : 1;
        return { result: (sign * Math.floor(Math.abs(a) / Math.abs(b))) & 0xff, exc: _NO_EXC };
    }
    if (op === Op.VMAX) return { result: a >= b ? a : b, exc: _NO_EXC };
    if (op === Op.VMIN) return { result: a <= b ? a : b, exc: _NO_EXC };
    throw new Error(`Unknown INT8 VU op: ${op}`);
}

function _vuArith(op, a, b, fmt, rm) {
    if (_FP_FMTS.has(fmt)) {
        return _arithFp(op, Number(a), Number(b), fmt, rm);
    }
    if (fmt === VU_FMT_I) return _arithInt8(op, a, b);
    return _arithUint8(op, a, b);
}

function _vuSqrt(val, fmt, rm) {
    return fpSqrt(Number(val), fmt, rm);
}

function _vuNeg(val, fmt) {
    if (_FP_FMTS.has(fmt)) {
        return { result: -Number(val), exc: _NO_EXC };
    }
    const raw = -val;
    return { result: raw & 0xff, exc: _intExc(raw) };
}

function _vuAbs(val, fmt) {
    if (_FP_FMTS.has(fmt)) {
        return { result: Math.abs(Number(val)), exc: _NO_EXC };
    }
    if (fmt === VU_FMT_U) {
        return { result: val & 0xff, exc: _NO_EXC };
    }
    // INT8
    if (val === -128) return { result: 128, exc: _NO_EXC };
    return { result: Math.abs(val) & 0xff, exc: _NO_EXC };
}

function _compare(a, b, cond) {
    if (cond === VU_CMP_EQ) return a === b;
    if (cond === VU_CMP_NE) return a !== b;
    if (cond === VU_CMP_LT) return a < b;
    if (cond === VU_CMP_LE) return a <= b;
    if (cond === VU_CMP_GT) return a > b;
    if (cond === VU_CMP_GE) return a >= b;
    throw new Error(`Unknown VU comparison condition: ${cond}`);
}

function _vuCmp(a, b, cond, fmt) {
    if (_FP_FMTS.has(fmt)) {
        const fa = Number(a);
        const fb = Number(b);
        if (Number.isNaN(fa) || Number.isNaN(fb)) {
            return cond === VU_CMP_NE ? 0xff : 0x00;
        }
        return _compare(fa, fb, cond) ? 0xff : 0x00;
    }
    return _compare(a, b, cond) ? 0xff : 0x00;
}

function _vuDot(valuesA, valuesB) {
    let acc = 0.0;
    for (let i = 0; i < valuesA.length; i++) {
        acc += valuesA[i] * valuesB[i];
    }
    return acc;
}

// ── VuRegisters ───────────────────────────────────────────────────

class VuRegisters {
    constructor() {
        this.va = 0;
        this.vb = 0;
        this.vc = 0;
        this.vm = 0;
        this.vl = 0;
        this.vfpsr = 0;
    }

    readPtr(code) {
        if (code === 0) return this.va;
        if (code === 1) return this.vb;
        if (code === 2) return this.vc;
        if (code === 3) return this.vm;
        throw new RangeError(`Invalid VU pointer code: ${code}`);
    }

    writeReg(code, val) {
        val &= 0xffff;
        if (code === 0) this.va = val;
        else if (code === 1) this.vb = val;
        else if (code === 2) this.vc = val;
        else if (code === 3) this.vm = val;
        else if (code === 4) this.vl = val;
        else throw new RangeError(`Invalid VU register code: ${code}`);
    }

    incPtr(code, amount) {
        const cur = this.readPtr(code);
        this.writeReg(code, (cur + amount) % MEMORY_SIZE);
    }

    reset() {
        this.va = 0;
        this.vb = 0;
        this.vc = 0;
        this.vm = 0;
        this.vl = 0;
        this.vfpsr = 0;
    }
}

// ── VuCommand ─────────────────────────────────────────────────────

class VuCommand {
    constructor(op, fmt, mode, cond, dstAddr, s1Addr, s2Addr, maskAddr, vl, imm, mnemonic, dstCode, s1Code, s2Code) {
        this.op = op;
        this.fmt = fmt;
        this.mode = mode;
        this.cond = cond;
        this.dstAddr = dstAddr;
        this.s1Addr = s1Addr;
        this.s2Addr = s2Addr;
        this.maskAddr = maskAddr;
        this.vl = vl;
        this.imm = imm;
        this.mnemonic = mnemonic;
        this.dstCode = dstCode;
        this.s1Code = s1Code;
        this.s2Code = s2Code;
        this._progress = 0;
    }
}

// ── VectorUnit ────────────────────────────────────────────────────

export class VectorUnit {
    constructor() {
        this.regs = new VuRegisters();
        this.state = VuState.IDLE;
        this._queue = [];
        this.fault = 0;
    }

    get queueDepth() {
        return this._queue.length;
    }

    get isFull() {
        return this._queue.length >= VU_QUEUE_DEPTH;
    }

    get isEmpty() {
        return this._queue.length === 0;
    }

    /** Active command memory windows for UI markers. null if idle. */
    get activeWindows() {
        if (this._queue.length === 0) return null;
        const cmd = this._queue[0];
        const sz = VU_FMT_ELEM_SIZE[cmd.fmt] || 1;
        const bytes = cmd.vl * sz;
        return { dst: cmd.dstAddr, src1: cmd.s1Addr, src2: cmd.s2Addr, bytes };
    }

    /** Snapshot of queued commands for UI. */
    get queueItems() {
        return this._queue.map((cmd, i) => ({
            label: `${cmd.mnemonic}.${_FMT_NAMES[cmd.fmt] ?? "?"}`,
            operands: `${_hex16(cmd.dstAddr)}, ${_hex16(cmd.s1Addr)}`,
            active: i === 0,
        }));
    }

    enqueue(cmd) {
        if (this.isFull) throw new Error("VU queue full");
        this._queue.push(cmd);
        this.state = VuState.BUSY;
    }

    /** Process one window of the front command. */
    tick(mem, rm) {
        if (this._queue.length === 0 || this.fault !== 0) return;
        const cmd = this._queue[0];
        const elemSize = VU_FMT_ELEM_SIZE[cmd.fmt] || 1;
        const windowSize = VU_WINDOW_SIZE[elemSize] || 4;
        const startIdx = cmd._progress;
        const endIdx = Math.min(startIdx + windowSize, cmd.vl);

        this._execWindow(mem, cmd, startIdx, endIdx, elemSize, rm);

        cmd._progress = endIdx;
        if (cmd._progress >= cmd.vl) {
            this._queue.shift();
            if (this._queue.length === 0) this.state = VuState.IDLE;
        }
    }

    /** Execute ALL remaining elements of ALL queued commands (VWAIT). */
    drainAll(mem, rm) {
        while (this._queue.length > 0 && this.fault === 0) {
            const cmd = this._queue[0];
            const elemSize = VU_FMT_ELEM_SIZE[cmd.fmt] || 1;

            // Execute remaining elements
            this._execWindow(mem, cmd, cmd._progress, cmd.vl, elemSize, rm);

            cmd._progress = cmd.vl;
            this._queue.shift();
        }
        this.state = VuState.IDLE;
    }

    flush() {
        this._queue.length = 0;
        this.state = VuState.IDLE;
    }

    reset() {
        this.regs.reset();
        this.flush();
        this.fault = 0;
    }

    // ── Internal execution ──────────────────────────────────────

    _execWindow(mem, cmd, startIdx, endIdx, elemSize, rm) {
        // OOB check before execution
        if (this._checkOob(cmd, elemSize)) {
            this.fault = ErrorCode.VU_OOB;
            this.flush();
            return;
        }

        const op = cmd.op;
        const fmt = cmd.fmt;

        if (op === Op.VDOT) {
            this._execDot(mem, cmd, elemSize, fmt, rm);
        } else if (op === Op.VMOV) {
            this._execMov(mem, cmd, startIdx, endIdx, elemSize);
        } else if (op === Op.VFILL) {
            this._execFill(mem, cmd, startIdx, endIdx, elemSize, fmt, rm);
        } else if (op === Op.VCMP) {
            this._execCmp(mem, cmd, startIdx, endIdx, elemSize, fmt);
        } else if (op === Op.VSEL) {
            this._execSel(mem, cmd, startIdx, endIdx, elemSize, fmt, rm);
        } else if (VU_UNARY_OPS.has(op)) {
            this._execUnary(mem, cmd, startIdx, endIdx, elemSize, fmt, rm);
        } else if (VU_ARITH_OPS.has(op)) {
            if (cmd.mode === VU_MODE_R) {
                this._execReduction(mem, cmd, elemSize, fmt, rm);
            } else {
                this._execArith(mem, cmd, startIdx, endIdx, elemSize, fmt, rm);
            }
        }
    }

    _checkOob(cmd, sz) {
        const vl = cmd.vl;
        // dst footprint depends on operation
        let dstBytes;
        if (cmd.op === Op.VCMP) {
            dstBytes = vl;
        } else if (cmd.op === Op.VDOT || cmd.mode === VU_MODE_R) {
            dstBytes = sz;
        } else {
            dstBytes = vl * sz;
        }
        if (cmd.dstAddr + dstBytes > MEMORY_SIZE) return true;
        // s1 footprint (VFILL and VSEL don't read s1 as vector)
        if (cmd.op !== Op.VFILL && cmd.op !== Op.VSEL) {
            if (cmd.s1Addr + vl * sz > MEMORY_SIZE) return true;
        }
        // s2 footprint for VV mode
        if (cmd.mode === VU_MODE_VV) {
            if (cmd.s2Addr + vl * sz > MEMORY_SIZE) return true;
        }
        // Mask pointer for VCMP/VSEL
        if (cmd.op === Op.VCMP || cmd.op === Op.VSEL) {
            if (cmd.maskAddr + vl > MEMORY_SIZE) return true;
        }
        return false;
    }

    _execMov(mem, cmd, startIdx, endIdx, sz) {
        for (let i = startIdx; i < endIdx; i++) {
            for (let b = 0; b < sz; b++) {
                mem.set(cmd.dstAddr + i * sz + b, mem.get(cmd.s1Addr + i * sz + b));
            }
        }
    }

    _execFill(mem, cmd, startIdx, endIdx, sz, fmt, rm) {
        let flags = 0;
        for (let i = startIdx; i < endIdx; i++) {
            const exc = _writeElem(mem, cmd.dstAddr + i * sz, fmt, cmd.imm, rm);
            flags |= _excToFlags(exc);
        }
        this.regs.vfpsr |= flags;
    }

    _execUnary(mem, cmd, startIdx, endIdx, sz, fmt, rm) {
        const op = cmd.op;
        let flags = 0;
        for (let i = startIdx; i < endIdx; i++) {
            const val = _readElem(mem, cmd.s1Addr + i * sz, fmt);
            let result, opExc;
            if (op === Op.VSQRT) {
                ({ result, exc: opExc } = _vuSqrt(val, fmt, rm));
            } else if (op === Op.VNEG) {
                ({ result, exc: opExc } = _vuNeg(val, fmt));
            } else {
                ({ result, exc: opExc } = _vuAbs(val, fmt));
            }
            flags |= _excToFlags(opExc);
            const wExc = _writeElem(mem, cmd.dstAddr + i * sz, fmt, result, rm);
            flags |= _excToFlags(wExc);
        }
        this.regs.vfpsr |= flags;
    }

    _execArith(mem, cmd, startIdx, endIdx, sz, fmt, rm) {
        let flags = 0;
        for (let i = startIdx; i < endIdx; i++) {
            const a = _readElem(mem, cmd.s1Addr + i * sz, fmt);
            let b;
            if (cmd.mode === VU_MODE_VV) {
                b = _readElem(mem, cmd.s2Addr + i * sz, fmt);
            } else {
                b = cmd.imm;
            }
            const { result, exc: opExc } = _vuArith(cmd.op, a, b, fmt, rm);
            flags |= _excToFlags(opExc);
            const wExc = _writeElem(mem, cmd.dstAddr + i * sz, fmt, result, rm);
            flags |= _excToFlags(wExc);
        }
        this.regs.vfpsr |= flags;
    }

    _execDot(mem, cmd, sz, fmt, rm) {
        const vl = cmd.vl;
        const valuesA = [];
        const valuesB = [];
        for (let i = 0; i < vl; i++) {
            valuesA.push(_readElem(mem, cmd.s1Addr + i * sz, fmt));
            valuesB.push(_readElem(mem, cmd.s2Addr + i * sz, fmt));
        }
        const result = _vuDot(valuesA, valuesB);
        const wExc = _writeElem(mem, cmd.dstAddr, fmt, result, rm);
        this.regs.vfpsr |= _excToFlags(wExc);
    }

    _execReduction(mem, cmd, sz, fmt, rm) {
        const vl = cmd.vl;
        let acc = _readElem(mem, cmd.s1Addr, fmt);
        let flags = 0;
        for (let i = 1; i < vl; i++) {
            const val = _readElem(mem, cmd.s1Addr + i * sz, fmt);
            const { result, exc: opExc } = _vuArith(cmd.op, acc, val, fmt, rm);
            acc = result;
            flags |= _excToFlags(opExc);
        }
        const wExc = _writeElem(mem, cmd.dstAddr, fmt, acc, rm);
        flags |= _excToFlags(wExc);
        this.regs.vfpsr |= flags;
    }

    _execCmp(mem, cmd, startIdx, endIdx, sz, fmt) {
        for (let i = startIdx; i < endIdx; i++) {
            const a = _readElem(mem, cmd.s1Addr + i * sz, fmt);
            const b = _readElem(mem, cmd.s2Addr + i * sz, fmt);
            mem.set(cmd.dstAddr + i, _vuCmp(a, b, cmd.cond, fmt));
        }
    }

    _execSel(mem, cmd, startIdx, endIdx, sz, fmt, rm) {
        for (let i = startIdx; i < endIdx; i++) {
            const maskByte = mem.get(cmd.maskAddr + i);
            if (maskByte === 0) {
                const alt = _readElem(mem, cmd.s2Addr + i * sz, fmt);
                _writeElem(mem, cmd.dstAddr + i * sz, fmt, alt, rm);
            }
        }
    }
}

export { VuCommand };
