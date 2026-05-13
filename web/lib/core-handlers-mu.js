/**
 * Matrix Unit instruction handlers and async MU executor.
 * Exported as a plain object; applied to CPU.prototype in core.js.
 */

import { bytesToFloat, floatToBytes, fpAdd, fpMul } from "./fp.js";

import {
    Op,
    CpuFault,
    ErrorCode,
    MU_FP_FMTS,
    MU_INT_FMTS,
    MU_FMT_ELEM_SIZE,
    decodeMfm,
    decodeVuRegs,
    VU_FMT_I,
} from "./core-types.js";

import { MuCommand, MuQueue, MuRegisters } from "./mu.js";

const MEM_SIZE = 65536;
const VU_FMT_F = 0;

const _FP_FMTS = new Set([0, 1, 2, 3, 4]);

// ── Element memory helpers ────────────────────────────────────────

function _muReadElem(mem, addr, fmt) {
    const sz = MU_FMT_ELEM_SIZE[fmt] ?? 1;
    if (_FP_FMTS.has(fmt)) {
        return bytesToFloat(
            Uint8Array.from({ length: sz }, (_, i) => mem.get(addr + i)),
            fmt,
        );
    }
    const val = mem.get(addr);
    return fmt === VU_FMT_I ? (val < 128 ? val : val - 256) : val;
}

function _muReadF32(mem, addr) {
    return bytesToFloat(
        Uint8Array.from({ length: 4 }, (_, i) => mem.get(addr + i)),
        VU_FMT_F,
    );
}

function _muWriteF32(mem, addr, val, rm) {
    const { data } = floatToBytes(Number(val), VU_FMT_F, rm);
    data.forEach((b, i) => mem.set(addr + i, b));
}

// ── muHandlers mixin ─────────────────────────────────────────────

export const muHandlers = {
    _initMu() {
        this._muQueue = new MuQueue();
        this._muRegs = new MuRegisters();
        this._mwaitPending = false;
        this._mwaitSize = 0;
    },

    _buildMuDispatch() {
        const d = this._dispatch;
        d[Op.MSET_IMM16] = (instr) => this._hMsetImm16(instr);
        d[Op.MSET_GPR] = (instr) => this._hMsetGpr(instr);
        d[Op.MFSTAT] = (instr) => this._hMfstat(instr);
        d[Op.MFCLR] = (instr) => this._hMfclr(instr);
        d[Op.MWAIT] = (instr) => this._hMwait(instr);
        d[Op.MMUL] = (instr) => this._hMasync(instr);
        d[Op.MMAD] = (instr) => this._hMasync(instr);
    },

    // ── Synchronous handlers ───────────────────────────────────────

    _hMsetImm16(instr) {
        const target = instr.operands[0];
        if (target > 5) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        this._muRegs.writeReg(target, (instr.operands[2] << 8) | instr.operands[1]);
        this.regs.ip += instr.size;
    },

    _hMsetGpr(instr) {
        const target = instr.operands[0];
        if (target > 5) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        const packed = instr.operands[1];
        const value =
            packed & 0x10
                ? this.regs.read(packed & 0x03)
                : (this.regs.read((packed >> 2) & 0x03) << 8) | this.regs.read(packed & 0x03);
        this._muRegs.writeReg(target, value);
        this.regs.ip += instr.size;
    },

    _hMfstat(instr) {
        const gpr = instr.operands[0];
        if (gpr > 3) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        this.regs.write(gpr, this._muRegs.mfpsr);
        this.regs.ip += instr.size;
    },

    _hMfclr(instr) {
        this._muRegs.mfpsr = 0;
        this.regs.ip += instr.size;
    },

    _hMwait(instr) {
        if (this._muQueue.fault !== 0) {
            const code = this._muQueue.fault;
            this._muQueue.fault = 0;
            throw new CpuFault(code, this.regs.ip);
        }
        if (!this._muQueue.isEmpty) {
            this._mwaitPending = true;
            this._mwaitSize = instr.size;
        } else {
            this.regs.ip += instr.size;
        }
    },

    // ── Async command issue ────────────────────────────────────────

    _hMasync(instr) {
        const mfm = instr.operands[0];
        const regsB = instr.operands[1];
        const [fmt, aCol, bCol, cCol] = decodeMfm(mfm);

        if (mfm & 0xc0) throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        if (!MU_FP_FMTS.has(fmt) && !MU_INT_FMTS.has(fmt)) throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        if (regsB & 0x03) throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        const [dst, s1, s2] = decodeVuRegs(regsB);
        if (dst > 2 || s1 > 2 || s2 > 2) throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);

        const mu = this._muRegs;
        const m = mu.mm,
            n = mu.mn,
            k = mu.mk;
        if (m === 0 || n === 0 || k === 0) {
            this.regs.ip += instr.size;
            return;
        }

        const sz = MU_FMT_ELEM_SIZE[fmt] ?? 1;
        const accumulate = instr.op === Op.MMAD;
        const cmd = new MuCommand(
            instr.op,
            fmt,
            aCol,
            bCol,
            cCol,
            accumulate,
            mu.readPtr(s1),
            mu.readPtr(s2),
            mu.readPtr(dst),
            m,
            n,
            k,
        );

        // Auto-increment MA / MB only; MC stays put so K-loop accumulation
        // does not need a re-MSET. Deduplicate when same code appears as both
        // A and B operand (advance once by the largest stride).
        const increments = new Map();
        for (const [code, inc] of [
            [s1, m * k * sz],
            [s2, k * n * sz],
        ]) {
            if (inc > 0) increments.set(code, Math.max(increments.get(code) ?? 0, inc));
        }
        for (const [code, inc] of increments) mu.incPtr(code, inc);

        while (this._muQueue.isFull) this.muTick();
        this._muQueue.enqueue(cmd);
        this.regs.ip += instr.size;
    },

    // ── MU async execution ─────────────────────────────────────────

    muTick() {
        if (this._muQueue.isEmpty || this._muQueue.fault !== 0) return;
        const cmd = this._muQueue.peek();
        const sz = MU_FMT_ELEM_SIZE[cmd.fmt] ?? 1;

        if (
            cmd.aAddr + cmd.m * cmd.k * sz > MEM_SIZE ||
            cmd.bAddr + cmd.k * cmd.n * sz > MEM_SIZE ||
            cmd.cAddr + cmd.m * cmd.n * 4 > MEM_SIZE
        ) {
            this._muQueue.fault = ErrorCode.VU_OOB;
            this._muQueue.flush();
            return;
        }

        this._muExecMmul(cmd, sz);
        this._muQueue.dequeue();
    },

    _muExecMmul(cmd, sz) {
        const rm = this.regs.fpu?.roundingMode ?? 0;
        const { m, n, k, fmt } = cmd;
        const isInt = MU_INT_FMTS.has(fmt);
        let flags = 0;

        for (let i = 0; i < m; i++) {
            for (let j = 0; j < n; j++) {
                const cOff = (cmd.cCol ? j * m + i : i * n + j) * 4;
                if (isInt) {
                    let acc = 0;
                    for (let kk = 0; kk < k; kk++) {
                        const aOff = (cmd.aCol ? kk * m + i : i * k + kk) * sz;
                        const bOff = (cmd.bCol ? j * k + kk : kk * n + j) * sz;
                        acc =
                            (acc +
                                _muReadElem(this.mem, cmd.aAddr + aOff, fmt) *
                                    _muReadElem(this.mem, cmd.bAddr + bOff, fmt)) >>>
                            0;
                    }
                    if (cmd.accumulate) {
                        let cOld = 0;
                        for (let b = 0; b < 4; b++) cOld |= this.mem.get(cmd.cAddr + cOff + b) << (b * 8);
                        acc = (acc + (cOld >>> 0)) >>> 0;
                    }
                    for (let b = 0; b < 4; b++) this.mem.set(cmd.cAddr + cOff + b, (acc >> (b * 8)) & 0xff);
                } else {
                    let acc = 0.0;
                    for (let kk = 0; kk < k; kk++) {
                        const aOff = (cmd.aCol ? kk * m + i : i * k + kk) * sz;
                        const bOff = (cmd.bCol ? j * k + kk : kk * n + j) * sz;
                        const a = Number(_muReadElem(this.mem, cmd.aAddr + aOff, fmt));
                        const b = Number(_muReadElem(this.mem, cmd.bAddr + bOff, fmt));
                        const { result: prod, exc: eMul } = fpMul(a, b, fmt, rm);
                        flags |=
                            (eMul.invalid ? 1 : 0) |
                            (eMul.overflow ? 4 : 0) |
                            (eMul.underflow ? 8 : 0) |
                            (eMul.inexact ? 16 : 0);
                        const { result: sum, exc: eAdd } = fpAdd(acc, prod, fmt, rm);
                        flags |=
                            (eAdd.invalid ? 1 : 0) |
                            (eAdd.overflow ? 4 : 0) |
                            (eAdd.underflow ? 8 : 0) |
                            (eAdd.inexact ? 16 : 0);
                        acc = sum;
                    }
                    if (cmd.accumulate) {
                        const cOld = _muReadF32(this.mem, cmd.cAddr + cOff);
                        const { result: sum2, exc: eAcc } = fpAdd(Number(cOld), acc, VU_FMT_F, rm);
                        flags |=
                            (eAcc.invalid ? 1 : 0) |
                            (eAcc.overflow ? 4 : 0) |
                            (eAcc.underflow ? 8 : 0) |
                            (eAcc.inexact ? 16 : 0);
                        acc = sum2;
                    }
                    _muWriteF32(this.mem, cmd.cAddr + cOff, acc, rm);
                }
            }
        }
        if (!isInt) this._muRegs.mfpsr |= flags;
    },

    _stepMwait() {
        this._cycles += 1;
        if (this._muQueue.isEmpty) {
            this._mwaitPending = false;
            this.regs.ip += this._mwaitSize;
            this._mwaitSize = 0;
        }
    },
};
