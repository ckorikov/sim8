/**
 * CPU core: instruction execution, dispatch tables, and control unit.
 * Helper types (Memory, ALU, RegisterFile, etc.) live in core-types.js.
 */

import {
    bytesToFloat,
    floatToBytes,
    fpAdd,
    fpSub,
    fpMul,
    fpDiv,
    fpSqrt,
    fpCmp,
    fpAbs,
    fpNeg,
    fpClassify,
} from "./fp.js";

import { VectorUnit, VuCommand } from "./vu.js";

import {
    // ISA symbols (re-exported by core-types from isa.js)
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
    VU_UNARY_OPS,
    VU_VV_ONLY_OPS,
    VU_INT_FMTS,
    VU_FMT_ELEM_SIZE,
    VU_MODE_VS,
    VU_MODE_VI,
    VU_MODE_R,
    decodeVfm,
    decodeVuRegs,
    // Core types
    Memory,
    ALU,
    RegisterFile,
    CpuFault,
    CpuState,
    ErrorCode,
    PAGE_SIZE,
    IO_START,
    SP_INIT,
    decode,
    intFromBytesLE,
    intToBytesLE,
} from "./core-types.js";

// Re-export public API from core-types so existing imports keep working
export { CpuState, ErrorCode, PAGE_SIZE, IO_START, SP_INIT, Memory };

// ── CPU ──────────────────────────────────────────────────────────

// Round to Nearest, ties to Even (IEEE 754 default)
function _roundRNE(x) {
    if (Math.abs(x - Math.trunc(x)) === 0.5) {
        // Tie case: pick the even neighbor
        const lo = Math.trunc(x);
        const hi = lo + Math.sign(x);
        return lo % 2 === 0 ? lo : hi;
    }
    return Math.round(x);
}

// Rounding mode index (FPCR bits 1:0) → rounding function (RNE/RTZ/RDN/RUP)
const _ROUND_FNS = [_roundRNE, Math.trunc, Math.floor, Math.ceil];

export class CPU {
    constructor({ arch = 2 } = {}) {
        this.mem = new Memory();
        this.regs = new RegisterFile(arch);
        this.state = CpuState.IDLE;
        this._steps = 0;
        this._cycles = 0;
        this._peakMem = 0;
        this._arch = arch;
        this._dispatch = {};

        this._buildDispatch();
        if (arch >= 2) {
            this._buildFpDispatch();
        }
        this.vu = null;
        this._vuWaiting = false;
        this._vwaitSize = 0;
        if (arch >= 3) {
            this.vu = new VectorUnit();
            this._buildVuDispatch();
        }

        let allIsa = arch < 2 ? ISA : ISA.concat(ISA_FP);
        if (arch >= 3) allIsa = allIsa.concat(ISA_VU);
        this._instrDef = {};
        this._opCost = {};
        for (const d of allIsa) {
            this._instrDef[d.op] = d;
            if (!d.formatDep) this._opCost[d.op] = d.cost;
        }
    }

    // ── Public API ───────────────────────────────────────────────

    load(code) {
        this.reset();
        this.mem.load(code);
        this._peakMem = code.length;
    }

    /** True when VU queue has pending work. */
    get vuBusy() {
        return this.vu !== null && !this.vu.isEmpty;
    }

    /** True when CPU is stalled on VWAIT. */
    get vuWaiting() {
        return this._vuWaiting;
    }

    /** Tick VU independently. Returns true if VU did work. */
    vuTick() {
        if (this.vu === null || this.vu.isEmpty) return false;
        this.vu.tick(this.mem, this._vuRoundingMode());
        if (this.vu.fault !== 0) {
            const code = this.vu.fault;
            this.vu.fault = 0;
            this._vuWaiting = false;
            this._enterFault(code);
            return false;
        }
        // VWAIT stall: each VU tick costs 1 CPU cycle
        if (this._vuWaiting) {
            this._cycles += 1;
            if (this.vu.isEmpty) {
                this._vuWaiting = false;
                this.regs.ip += this._vwaitSize;
                this._vwaitSize = 0;
            }
        }
        return true;
    }

    /** Execute one CPU instruction. Does NOT touch VU. */
    step() {
        if (this.state === CpuState.FAULT) return false;
        if (this.state === CpuState.HALTED) return false;
        if (this._vuWaiting) return false; // CPU stalled on VWAIT

        if (this.state === CpuState.IDLE) {
            this.state = CpuState.RUNNING;
        }

        let instr;
        try {
            instr = decode(this.mem, this.regs.ip, this._arch);
        } catch (e) {
            if (e instanceof CpuFault) {
                this._enterFault(e.code);
                return false;
            }
            throw e;
        }

        if (instr.op === Op.HLT) {
            this.state = CpuState.HALTED;
            return false;
        }

        try {
            const handler = this._dispatch[instr.op];
            handler(instr);
        } catch (e) {
            if (e instanceof CpuFault) {
                this._enterFault(e.code);
                return false;
            }
            throw e;
        }

        this._steps += 1;
        this._cycles += this._computeCost(instr);
        const used = this.mem.usedBytes();
        if (used > this._peakMem) this._peakMem = used;
        return this.state === CpuState.RUNNING;
    }

    run(maxSteps = 100000) {
        for (let i = 0; i < maxSteps; i++) {
            this.vuTick();
            if (!this.step() && !this.vuBusy) break;
        }
        return this.state;
    }

    pause() {
        if (this.state === CpuState.RUNNING) {
            this.state = CpuState.IDLE;
        }
    }

    reset() {
        this.mem.reset();
        this.regs.reset(this._arch);
        this.state = CpuState.IDLE;
        this._steps = 0;
        this._cycles = 0;
        this._peakMem = 0;
        this._vuWaiting = false;
        this._vwaitSize = 0;
        if (this.vu !== null) this.vu.reset();
    }

    get steps() {
        return this._steps;
    }
    get cycles() {
        return this._cycles;
    }
    get peakMem() {
        return this._peakMem;
    }

    get a() {
        return this.regs.a;
    }
    get b() {
        return this.regs.b;
    }
    get c() {
        return this.regs.c;
    }
    get d() {
        return this.regs.d;
    }
    get sp() {
        return this.regs.sp;
    }
    get dp() {
        return this.regs.dp;
    }
    get ip() {
        return this.regs.ip;
    }
    get zero() {
        return this.regs.flags.z;
    }
    get carry() {
        return this.regs.flags.c;
    }
    get fault() {
        return this.regs.flags.f;
    }
    get fpu() {
        return this.regs.fpu;
    }

    display() {
        const chars = [];
        for (let addr = IO_START; addr < PAGE_SIZE; addr++) {
            const b = this.mem.get(addr);
            chars.push(b >= 0x21 && b <= 0x7e ? String.fromCharCode(b) : " ");
        }
        return chars.join("").trimEnd();
    }

    // ── Fault handling ─────────────────────────────────────────────

    _enterFault(code) {
        this.regs.flags.f = true;
        this.regs.a = code;
        this.state = CpuState.FAULT;
    }

    // ── Cost accounting ────────────────────────────────────────────

    // Cycle cost per FP format for memory-accessing FP instructions.
    // Derived from FP_FMT_WIDTH (fmt 0..4): bits / 8 = bytes transferred.
    static _FP_FMT_MEM_COST = Array.from({ length: 5 }, (_, fmt) => FP_FMT_WIDTH[fmt] / 8);

    _computeCost(instr) {
        const op = instr.op;
        const d = this._instrDef[op];
        if (d?.formatDep) {
            const fmt = instr.operands[0] % 8;
            return (CPU._FP_FMT_MEM_COST[fmt] ?? 4) + d.cost;
        }
        return this._opCost[op] ?? 1;
    }

    // ── Address resolution ─────────────────────────────────────────

    _directAddr(offset) {
        return this.regs.dp * PAGE_SIZE + offset;
    }

    _indirectAddr(encoded) {
        const [reg, offset] = decodeRegaddr(encoded);
        if (reg > Reg.SP) {
            throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        }

        const base = reg === Reg.SP ? this.regs.sp : this.regs.read(reg);
        const pageOffset = base + offset;

        if (pageOffset < 0 || pageOffset >= PAGE_SIZE) {
            throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
        }

        if (reg === Reg.SP) return pageOffset;
        return this.regs.dp * PAGE_SIZE + pageOffset;
    }

    // ── Register validation ────────────────────────────────────────

    _decodeGpr(code) {
        if (code > Reg.D) {
            throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        }
        return code;
    }

    _decodeGprOrSp(code) {
        if (code > Reg.SP) {
            throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        }
        return code;
    }

    _decodeGprOrDp(code) {
        if (code > Reg.D && code !== Reg.DP) {
            throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        }
        return code;
    }

    _decodeMovReg(code) {
        if (code > Reg.DP) {
            throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        }
        return code;
    }

    // ── Source resolvers ───────────────────────────────────────────

    _srcRegaddr(instr) {
        return this.mem.get(this._indirectAddr(instr.operands[1]));
    }

    _srcAddr(instr) {
        return this.mem.get(this._directAddr(instr.operands[1]));
    }

    _srcConst(instr) {
        return instr.operands[1];
    }

    _srcStkReg(instr) {
        const code = this._decodeGprOrSp(instr.operands[1]);
        return this.regs.read(code);
    }

    _srcGprReg(instr) {
        const code = this._decodeGpr(instr.operands[1]);
        return this.regs.read(code);
    }

    _srcMuldivReg(instr) {
        const code = this._decodeGpr(instr.operands[0]);
        return this.regs.read(code);
    }

    _srcMuldivRegaddr(instr) {
        return this.mem.get(this._indirectAddr(instr.operands[0]));
    }

    _srcMuldivAddr(instr) {
        return this.mem.get(this._directAddr(instr.operands[0]));
    }

    _srcMuldivConst(instr) {
        return instr.operands[0];
    }

    // ── Stack helpers ──────────────────────────────────────────────

    _doPush(value) {
        if (this.regs.sp === 0) {
            throw new CpuFault(ErrorCode.STACK_OVERFLOW, this.regs.ip);
        }
        this.mem.set(this.regs.sp, value);
        this.regs.sp = this.regs.sp - 1;
    }

    _doPop() {
        if (this.regs.sp >= SP_INIT) {
            throw new CpuFault(ErrorCode.STACK_UNDERFLOW, this.regs.ip);
        }
        this.regs.sp = this.regs.sp + 1;
        return this.mem.get(this.regs.sp);
    }

    // ── Handler factories ──────────────────────────────────────────

    _makeAlu2op(aluFn, resolveSrc, writeback = true) {
        return (instr) => {
            const destCode = this._decodeGprOrSp(instr.operands[0]);
            const right = resolveSrc(instr);
            const left = this.regs.read(destCode);
            const [result, carry, zero] = aluFn(left, right);
            this.regs.flags.c = carry;
            this.regs.flags.z = zero;
            if (writeback) {
                this.regs.write(destCode, result);
            }
            this.regs.ip += instr.size;
        };
    }

    _makeBitwise2op(aluFn, resolveSrc) {
        return (instr) => {
            const destCode = this._decodeGpr(instr.operands[0]);
            const right = resolveSrc(instr);
            const left = this.regs.read(destCode);
            const [result, zero] = aluFn(left, right);
            this.regs.flags.c = false;
            this.regs.flags.z = zero;
            this.regs.write(destCode, result);
            this.regs.ip += instr.size;
        };
    }

    _makeShift2op(aluFn, resolveSrc) {
        return (instr) => {
            const destCode = this._decodeGpr(instr.operands[0]);
            const count = resolveSrc(instr);
            const value = this.regs.read(destCode);
            if (count === 0) {
                this.regs.flags.z = value === 0;
            } else {
                const [result, carry, zero] = aluFn(value, count);
                this.regs.flags.c = carry;
                this.regs.flags.z = zero;
                this.regs.write(destCode, result);
            }
            this.regs.ip += instr.size;
        };
    }

    _makeJcc(condition, isReg) {
        return (instr) => {
            let target;
            if (isReg) {
                const code = this._decodeGpr(instr.operands[0]);
                target = this.regs.read(code);
            } else {
                target = instr.operands[0];
            }
            if (condition()) {
                this.regs.ip = target;
            } else {
                this.regs.ip += instr.size;
            }
        };
    }

    _makeMuldiv(aluFn, resolveSrc) {
        return (instr) => {
            const right = resolveSrc(instr);
            const [result, carry, zero] = aluFn(this.regs.a, right);
            this.regs.flags.c = carry;
            this.regs.flags.z = zero;
            this.regs.a = result;
            this.regs.ip += instr.size;
        };
    }

    _makeDiv(resolveSrc) {
        return (instr) => {
            const right = resolveSrc(instr);
            if (right === 0) {
                throw new CpuFault(ErrorCode.DIV_ZERO, this.regs.ip);
            }
            const [result, carry, zero] = ALU.div(this.regs.a, right);
            this.regs.flags.c = carry;
            this.regs.flags.z = zero;
            this.regs.a = result;
            this.regs.ip += instr.size;
        };
    }

    // ── Integer dispatch table ─────────────────────────────────────

    _buildDispatch() {
        const d = this._dispatch;

        // -- MOV variants --
        d[Op.MOV_REG_REG] = (instr) => {
            const dest = this._decodeMovReg(instr.operands[0]);
            const src = this._decodeMovReg(instr.operands[1]);
            this.regs.write(dest, this.regs.read(src));
            this.regs.ip += instr.size;
        };
        d[Op.MOV_REG_ADDR] = (instr) => {
            const dest = this._decodeMovReg(instr.operands[0]);
            this.regs.write(dest, this.mem.get(this._directAddr(instr.operands[1])));
            this.regs.ip += instr.size;
        };
        d[Op.MOV_REG_REGADDR] = (instr) => {
            const dest = this._decodeMovReg(instr.operands[0]);
            this.regs.write(dest, this.mem.get(this._indirectAddr(instr.operands[1])));
            this.regs.ip += instr.size;
        };
        d[Op.MOV_ADDR_REG] = (instr) => {
            const addr = this._directAddr(instr.operands[0]);
            const src = this._decodeMovReg(instr.operands[1]);
            this.mem.set(addr, this.regs.read(src));
            this.regs.ip += instr.size;
        };
        d[Op.MOV_REGADDR_REG] = (instr) => {
            const addr = this._indirectAddr(instr.operands[0]);
            const src = this._decodeMovReg(instr.operands[1]);
            this.mem.set(addr, this.regs.read(src));
            this.regs.ip += instr.size;
        };
        d[Op.MOV_REG_CONST] = (instr) => {
            const dest = this._decodeMovReg(instr.operands[0]);
            this.regs.write(dest, instr.operands[1]);
            this.regs.ip += instr.size;
        };
        d[Op.MOV_ADDR_CONST] = (instr) => {
            const addr = this._directAddr(instr.operands[0]);
            this.mem.set(addr, instr.operands[1]);
            this.regs.ip += instr.size;
        };
        d[Op.MOV_REGADDR_CONST] = (instr) => {
            const addr = this._indirectAddr(instr.operands[0]);
            this.mem.set(addr, instr.operands[1]);
            this.regs.ip += instr.size;
        };

        // -- ADD / SUB (4 variants each) --
        const srcStk = (i) => this._srcStkReg(i);
        const srcRA = (i) => this._srcRegaddr(i);
        const srcA = (i) => this._srcAddr(i);
        const srcC = (i) => this._srcConst(i);

        for (const [base, aluFn] of [
            [Op.ADD_REG_REG, ALU.add],
            [Op.SUB_REG_REG, ALU.sub],
        ]) {
            d[base + 0] = this._makeAlu2op(aluFn, srcStk);
            d[base + 1] = this._makeAlu2op(aluFn, srcRA);
            d[base + 2] = this._makeAlu2op(aluFn, srcA);
            d[base + 3] = this._makeAlu2op(aluFn, srcC);
        }

        // -- INC / DEC --
        d[Op.INC_REG] = (instr) => {
            const code = this._decodeGprOrSp(instr.operands[0]);
            const [result, carry, zero] = ALU.inc(this.regs.read(code));
            this.regs.flags.c = carry;
            this.regs.flags.z = zero;
            this.regs.write(code, result);
            this.regs.ip += instr.size;
        };
        d[Op.DEC_REG] = (instr) => {
            const code = this._decodeGprOrSp(instr.operands[0]);
            const [result, carry, zero] = ALU.dec(this.regs.read(code));
            this.regs.flags.c = carry;
            this.regs.flags.z = zero;
            this.regs.write(code, result);
            this.regs.ip += instr.size;
        };

        // -- CMP (4 variants, SUB without writeback) --
        d[Op.CMP_REG_REG] = this._makeAlu2op(ALU.sub, srcStk, false);
        d[Op.CMP_REG_REGADDR] = this._makeAlu2op(ALU.sub, srcRA, false);
        d[Op.CMP_REG_ADDR] = this._makeAlu2op(ALU.sub, srcA, false);
        d[Op.CMP_REG_CONST] = this._makeAlu2op(ALU.sub, srcC, false);

        // -- JMP --
        d[Op.JMP_REG] = (instr) => {
            const code = this._decodeGpr(instr.operands[0]);
            this.regs.ip = this.regs.read(code);
        };
        d[Op.JMP_ADDR] = (instr) => {
            this.regs.ip = instr.operands[0];
        };

        // -- Conditional jumps --
        d[Op.JC_REG] = this._makeJcc(() => this.regs.flags.c, true);
        d[Op.JC_ADDR] = this._makeJcc(() => this.regs.flags.c, false);
        d[Op.JNC_REG] = this._makeJcc(() => !this.regs.flags.c, true);
        d[Op.JNC_ADDR] = this._makeJcc(() => !this.regs.flags.c, false);
        d[Op.JZ_REG] = this._makeJcc(() => this.regs.flags.z, true);
        d[Op.JZ_ADDR] = this._makeJcc(() => this.regs.flags.z, false);
        d[Op.JNZ_REG] = this._makeJcc(() => !this.regs.flags.z, true);
        d[Op.JNZ_ADDR] = this._makeJcc(() => !this.regs.flags.z, false);
        d[Op.JA_REG] = this._makeJcc(() => !this.regs.flags.c && !this.regs.flags.z, true);
        d[Op.JA_ADDR] = this._makeJcc(() => !this.regs.flags.c && !this.regs.flags.z, false);
        d[Op.JNA_REG] = this._makeJcc(() => this.regs.flags.c || this.regs.flags.z, true);
        d[Op.JNA_ADDR] = this._makeJcc(() => this.regs.flags.c || this.regs.flags.z, false);

        // -- PUSH (4 variants) --
        d[Op.PUSH_REG] = (instr) => {
            const code = this._decodeGprOrDp(instr.operands[0]);
            this._doPush(this.regs.read(code));
            this.regs.ip += instr.size;
        };
        d[Op.PUSH_REGADDR] = (instr) => {
            const addr = this._indirectAddr(instr.operands[0]);
            this._doPush(this.mem.get(addr));
            this.regs.ip += instr.size;
        };
        d[Op.PUSH_ADDR] = (instr) => {
            const addr = this._directAddr(instr.operands[0]);
            this._doPush(this.mem.get(addr));
            this.regs.ip += instr.size;
        };
        d[Op.PUSH_CONST] = (instr) => {
            this._doPush(instr.operands[0]);
            this.regs.ip += instr.size;
        };

        // -- POP --
        d[Op.POP_REG] = (instr) => {
            const code = this._decodeGprOrDp(instr.operands[0]);
            this.regs.write(code, this._doPop());
            this.regs.ip += instr.size;
        };

        // -- CALL / RET --
        d[Op.CALL_REG] = (instr) => {
            const code = this._decodeGpr(instr.operands[0]);
            const target = this.regs.read(code);
            this._doPush(this.regs.ip + instr.size);
            this.regs.ip = target;
        };
        d[Op.CALL_ADDR] = (instr) => {
            const target = instr.operands[0];
            this._doPush(this.regs.ip + instr.size);
            this.regs.ip = target;
        };
        d[Op.RET] = (_instr) => {
            this.regs.ip = this._doPop();
        };

        // -- MUL (4 variants) --
        const mdReg = (i) => this._srcMuldivReg(i);
        const mdRA = (i) => this._srcMuldivRegaddr(i);
        const mdA = (i) => this._srcMuldivAddr(i);
        const mdC = (i) => this._srcMuldivConst(i);

        d[Op.MUL_REG] = this._makeMuldiv(ALU.mul, mdReg);
        d[Op.MUL_REGADDR] = this._makeMuldiv(ALU.mul, mdRA);
        d[Op.MUL_ADDR] = this._makeMuldiv(ALU.mul, mdA);
        d[Op.MUL_CONST] = this._makeMuldiv(ALU.mul, mdC);

        // -- DIV (4 variants) --
        d[Op.DIV_REG] = this._makeDiv(mdReg);
        d[Op.DIV_REGADDR] = this._makeDiv(mdRA);
        d[Op.DIV_ADDR] = this._makeDiv(mdA);
        d[Op.DIV_CONST] = this._makeDiv(mdC);

        // -- Bitwise: AND/OR/XOR (4 variants each) --
        const srcGpr = (i) => this._srcGprReg(i);

        for (const [base, aluFn] of [
            [Op.AND_REG_REG, ALU.and_op],
            [Op.OR_REG_REG, ALU.or_op],
            [Op.XOR_REG_REG, ALU.xor_op],
        ]) {
            d[base + 0] = this._makeBitwise2op(aluFn, srcGpr);
            d[base + 1] = this._makeBitwise2op(aluFn, srcRA);
            d[base + 2] = this._makeBitwise2op(aluFn, srcA);
            d[base + 3] = this._makeBitwise2op(aluFn, srcC);
        }

        // -- NOT --
        d[Op.NOT_REG] = (instr) => {
            const code = this._decodeGpr(instr.operands[0]);
            const [result, zero] = ALU.not_op(this.regs.read(code));
            this.regs.flags.c = false;
            this.regs.flags.z = zero;
            this.regs.write(code, result);
            this.regs.ip += instr.size;
        };

        // -- Shift: SHL/SHR (4 variants each) --
        for (const [base, aluFn] of [
            [Op.SHL_REG_REG, ALU.shl],
            [Op.SHR_REG_REG, ALU.shr],
        ]) {
            d[base + 0] = this._makeShift2op(aluFn, srcGpr);
            d[base + 1] = this._makeShift2op(aluFn, srcRA);
            d[base + 2] = this._makeShift2op(aluFn, srcA);
            d[base + 3] = this._makeShift2op(aluFn, srcC);
        }
    }

    // ── FPU access ─────────────────────────────────────────────────

    get _fpu() {
        const fpu = this.regs.fpu;
        if (fpu === null) {
            throw new Error("FPU not available (arch < 2)");
        }
        return fpu;
    }

    _validateFpm(fpm) {
        if (!validateFpm(fpm)) {
            throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
        }
        return decodeFpm(fpm);
    }

    // ── FP memory helpers ──────────────────────────────────────────

    _fpReadMemRaw(addr, fmt) {
        const width = FP_FMT_WIDTH[fmt];
        const nbytes = width / 8;
        const pageOffset = addr % PAGE_SIZE;
        if (pageOffset + nbytes > PAGE_SIZE) {
            throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
        }
        const data = new Uint8Array(nbytes);
        for (let i = 0; i < nbytes; i++) {
            data[i] = this.mem.get(addr + i);
        }
        return data;
    }

    _fpReadMem(addr, fmt) {
        const data = this._fpReadMemRaw(addr, fmt);
        return bytesToFloat(data, fmt);
    }

    _fpWriteMemRaw(addr, fmt, data) {
        const width = FP_FMT_WIDTH[fmt];
        const nbytes = width / 8;
        const pageOffset = addr % PAGE_SIZE;
        if (pageOffset + nbytes > PAGE_SIZE) {
            throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
        }
        for (let i = 0; i < data.length; i++) {
            this.mem.set(addr + i, data[i]);
        }
    }

    // ── FP register helpers ────────────────────────────────────────

    _fpReadReg(pos, fmt, phys = 0) {
        const raw = this._fpu.readBits(pos, fmt, phys);
        const width = FP_FMT_WIDTH[fmt];
        const data = intToBytesLE(raw, width / 8);
        return bytesToFloat(data, fmt);
    }

    _fpWriteReg(pos, fmt, value, phys = 0) {
        const { data, exc } = floatToBytes(value, fmt, this._fpu.roundingMode);
        this._fpu.accumulateExceptions(exc);
        const raw = intFromBytesLE(data);
        this._fpu.writeBits(pos, fmt, raw, phys);
    }

    // ── FP dispatch table ──────────────────────────────────────────

    _buildFpDispatch() {
        const d = this._dispatch;

        // -- FMOV load/store (128-131) --
        d[Op.FMOV_FP_ADDR] = (instr) => {
            this._fmovLoad(instr, this._directAddr(instr.operands[1]));
        };
        d[Op.FMOV_FP_REGADDR] = (instr) => {
            this._fmovLoad(instr, this._indirectAddr(instr.operands[1]));
        };
        d[Op.FMOV_ADDR_FP] = (instr) => {
            this._fmovStore(instr, this._directAddr(instr.operands[1]));
        };
        d[Op.FMOV_REGADDR_FP] = (instr) => {
            this._fmovStore(instr, this._indirectAddr(instr.operands[1]));
        };

        // -- FMOV immediate (161-162) --
        d[Op.FMOV_FP_IMM8] = (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            if (fmt !== FP_FMT_O3 && fmt !== FP_FMT_O2) {
                throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
            }
            this._fpu.writeBits(pos, fmt, instr.operands[1], phys);
            this.regs.ip += instr.size;
        };
        d[Op.FMOV_FP_IMM16] = (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            if (fmt !== FP_FMT_H && fmt !== FP_FMT_BF) {
                throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
            }
            const imm16 = instr.operands[1] | (instr.operands[2] << 8);
            this._fpu.writeBits(pos, fmt, imm16, phys);
            this.regs.ip += instr.size;
        };

        // -- FP arith mem (132-141) --
        const dAddr = (off) => this._directAddr(off);
        const iAddr = (enc) => this._indirectAddr(enc);

        d[Op.FADD_FP_ADDR] = this._makeFpArithMem(fpAdd, dAddr);
        d[Op.FADD_FP_REGADDR] = this._makeFpArithMem(fpAdd, iAddr);
        d[Op.FSUB_FP_ADDR] = this._makeFpArithMem(fpSub, dAddr);
        d[Op.FSUB_FP_REGADDR] = this._makeFpArithMem(fpSub, iAddr);
        d[Op.FMUL_FP_ADDR] = this._makeFpArithMem(fpMul, dAddr);
        d[Op.FMUL_FP_REGADDR] = this._makeFpArithMem(fpMul, iAddr);
        d[Op.FDIV_FP_ADDR] = this._makeFpArithMem(fpDiv, dAddr);
        d[Op.FDIV_FP_REGADDR] = this._makeFpArithMem(fpDiv, iAddr);
        d[Op.FCMP_FP_ADDR] = this._makeFpCmpMem(dAddr);
        d[Op.FCMP_FP_REGADDR] = this._makeFpCmpMem(iAddr);

        // -- Unary (142-144) --
        d[Op.FABS_FP] = (instr) => this._fpUnaryBitwise(instr, fpAbs);
        d[Op.FNEG_FP] = (instr) => this._fpUnaryBitwise(instr, fpNeg);
        d[Op.FSQRT_FP] = (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            const val = this._fpReadReg(pos, fmt, phys);
            const { result, exc } = fpSqrt(val, fmt, this._fpu.roundingMode);
            this._fpu.accumulateExceptions(exc);
            this._fpWriteReg(pos, fmt, result, phys);
            this.regs.ip += instr.size;
        };

        // -- FMOV reg-reg (145) --
        d[Op.FMOV_RR] = (instr) => {
            const [dstPhys, dstPos, dstFmt] = this._validateFpm(instr.operands[0]);
            const [srcPhys, srcPos, srcFmt] = this._validateFpm(instr.operands[1]);
            if (dstFmt !== srcFmt) {
                throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
            }
            const raw = this._fpu.readBits(srcPos, srcFmt, srcPhys);
            this._fpu.writeBits(dstPos, dstFmt, raw, dstPhys);
            this.regs.ip += instr.size;
        };

        // -- FCVT (146) --
        d[Op.FCVT_FP_FP] = (instr) => {
            const [dstPhys, dstPos, dstFmt] = this._validateFpm(instr.operands[0]);
            const [srcPhys, srcPos, srcFmt] = this._validateFpm(instr.operands[1]);
            const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
            this._fpWriteReg(dstPos, dstFmt, srcVal, dstPhys);
            this.regs.ip += instr.size;
        };

        // -- FITOF (147) --
        d[Op.FITOF_FP_GPR] = (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            const gpr = this._decodeGpr(instr.operands[1]);
            const intVal = this.regs.read(gpr);
            this._fpWriteReg(pos, fmt, intVal, phys);
            this.regs.ip += instr.size;
        };

        // -- FFTOI (148) --
        d[Op.FFTOI_GPR_FP] = (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            const gpr = this._decodeGpr(instr.operands[1]);
            const fpVal = this._fpReadReg(pos, fmt, phys);

            let excInvalid = false;
            let excInexact = false;
            let result;

            if (Number.isNaN(fpVal)) {
                result = 0;
                excInvalid = true;
            } else if (!Number.isFinite(fpVal)) {
                result = fpVal > 0 ? 255 : 0;
                excInvalid = true;
            } else {
                const rounded = _ROUND_FNS[this._fpu.roundingMode](fpVal);
                if (rounded !== fpVal) excInexact = true;
                if (rounded > 255) result = 255;
                else if (rounded < 0) result = 0;
                else result = rounded;
            }

            this._fpu.accumulateExceptions({
                invalid: excInvalid,
                divZero: false,
                overflow: false,
                underflow: false,
                inexact: excInexact,
            });
            this.regs.write(gpr, result);
            this.regs.ip += instr.size;
        };

        // -- FSTAT (149) --
        d[Op.FSTAT_GPR] = (instr) => {
            const gpr = this._decodeGpr(instr.operands[0]);
            this.regs.write(gpr, this._fpu.fpsr);
            this.regs.ip += instr.size;
        };

        // -- FCFG (150) --
        d[Op.FCFG_GPR] = (instr) => {
            const gpr = this._decodeGpr(instr.operands[0]);
            this.regs.write(gpr, this._fpu.fpcr);
            this.regs.ip += instr.size;
        };

        // -- FSCFG (151) --
        d[Op.FSCFG_GPR] = (instr) => {
            const gpr = this._decodeGpr(instr.operands[0]);
            this._fpu.fpcr = this.regs.read(gpr) & 0x03;
            this.regs.ip += instr.size;
        };

        // -- FCLR (152) --
        d[Op.FCLR] = (instr) => {
            this._fpu.fpsr = 0;
            this.regs.ip += instr.size;
        };

        // -- Reg-reg arith (153-156) --
        d[Op.FADD_RR] = this._makeFpArithRR(fpAdd);
        d[Op.FSUB_RR] = this._makeFpArithRR(fpSub);
        d[Op.FMUL_RR] = this._makeFpArithRR(fpMul);
        d[Op.FDIV_RR] = this._makeFpArithRR(fpDiv);

        // -- FCMP_RR (157) --
        d[Op.FCMP_RR] = (instr) => {
            const [dstPhys, dstPos, dstFmt] = this._validateFpm(instr.operands[0]);
            const [srcPhys, srcPos, srcFmt] = this._validateFpm(instr.operands[1]);
            if (dstFmt !== srcFmt) {
                throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
            }
            const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);
            const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
            const { zero, carry, exc } = fpCmp(dstVal, srcVal);
            this._fpu.accumulateExceptions(exc);
            this.regs.flags.z = zero;
            this.regs.flags.c = carry;
            this.regs.ip += instr.size;
        };

        // -- FCLASS (158) --
        d[Op.FCLASS_GPR_FP] = (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            const gpr = this._decodeGpr(instr.operands[1]);
            const raw = this._fpu.readBits(pos, fmt, phys);
            const width = FP_FMT_WIDTH[fmt];
            const data = intToBytesLE(raw, width / 8);
            const val = bytesToFloat(data, fmt);
            const mask = fpClassify(val, raw, width, fmt);
            this.regs.write(gpr, mask);
            this.regs.ip += instr.size;
        };

        // -- FMADD (159-160) --
        d[Op.FMADD_FP_FP_ADDR] = (instr) => {
            this._doFmadd(instr, this._directAddr(instr.operands[2]));
        };
        d[Op.FMADD_FP_FP_REGADDR] = (instr) => {
            this._doFmadd(instr, this._indirectAddr(instr.operands[2]));
        };
    }

    // ── FP handler factories ───────────────────────────────────────

    _makeFpArithMem(arithFn, resolveAddr) {
        return (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            const addr = resolveAddr(instr.operands[1]);
            const regVal = this._fpReadReg(pos, fmt, phys);
            const memVal = this._fpReadMem(addr, fmt);
            const { result, exc } = arithFn(regVal, memVal, fmt, this._fpu.roundingMode);
            this._fpu.accumulateExceptions(exc);
            this._fpWriteReg(pos, fmt, result, phys);
            this.regs.ip += instr.size;
        };
    }

    _makeFpCmpMem(resolveAddr) {
        return (instr) => {
            const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
            const addr = resolveAddr(instr.operands[1]);
            const regVal = this._fpReadReg(pos, fmt, phys);
            const memVal = this._fpReadMem(addr, fmt);
            const { zero, carry, exc } = fpCmp(regVal, memVal);
            this._fpu.accumulateExceptions(exc);
            this.regs.flags.z = zero;
            this.regs.flags.c = carry;
            this.regs.ip += instr.size;
        };
    }

    _makeFpArithRR(arithFn) {
        return (instr) => {
            const [dstPhys, dstPos, dstFmt] = this._validateFpm(instr.operands[0]);
            const [srcPhys, srcPos, srcFmt] = this._validateFpm(instr.operands[1]);
            if (dstFmt !== srcFmt) {
                throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
            }
            const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);
            const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
            const { result, exc } = arithFn(dstVal, srcVal, dstFmt, this._fpu.roundingMode);
            this._fpu.accumulateExceptions(exc);
            this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
            this.regs.ip += instr.size;
        };
    }

    // ── FP individual handlers ─────────────────────────────────────

    _fmovLoad(instr, addr) {
        const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
        const data = this._fpReadMemRaw(addr, fmt);
        const raw = intFromBytesLE(data);
        this._fpu.writeBits(pos, fmt, raw, phys);
        this.regs.ip += instr.size;
    }

    _fmovStore(instr, addr) {
        const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
        const raw = this._fpu.readBits(pos, fmt, phys);
        const data = intToBytesLE(raw, FP_FMT_WIDTH[fmt] / 8);
        this._fpWriteMemRaw(addr, fmt, data);
        this.regs.ip += instr.size;
    }

    _fpUnaryBitwise(instr, fn) {
        const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
        const raw = this._fpu.readBits(pos, fmt, phys);
        const result = fn(raw, FP_FMT_WIDTH[fmt]);
        this._fpu.writeBits(pos, fmt, result, phys);
        this.regs.ip += instr.size;
    }

    _doFmadd(instr, addr) {
        const [dstPhys, dstPos, dstFmt] = this._validateFpm(instr.operands[0]);
        const [srcPhys, srcPos, srcFmt] = this._validateFpm(instr.operands[1]);
        if (dstFmt !== srcFmt) {
            throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
        }

        const srcVal = this._fpReadReg(srcPos, srcFmt, srcPhys);
        const memVal = this._fpReadMem(addr, dstFmt);
        const dstVal = this._fpReadReg(dstPos, dstFmt, dstPhys);

        const { result: mulResult, exc: mulExc } = fpMul(srcVal, memVal, dstFmt, this._fpu.roundingMode);
        const { result, exc: addExc } = fpAdd(mulResult, dstVal, dstFmt, this._fpu.roundingMode);

        this._fpu.accumulateExceptions({
            invalid: mulExc.invalid || addExc.invalid,
            divZero: mulExc.divZero || addExc.divZero,
            overflow: mulExc.overflow || addExc.overflow,
            underflow: mulExc.underflow || addExc.underflow,
            inexact: mulExc.inexact || addExc.inexact,
        });
        this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
        this.regs.ip += instr.size;
    }

    // ── VU helpers ────────────────────────────────────────────────────

    _vuRoundingMode() {
        const fpu = this.regs.fpu;
        return fpu !== null ? fpu.roundingMode : 0;
    }

    get vuRegs() {
        return this.vu !== null ? this.vu.regs : null;
    }

    get vuState() {
        return this.vu !== null ? this.vu.state : null;
    }

    get vuQueueItems() {
        return this.vu !== null ? this.vu.queueItems : [];
    }

    // ── VU dispatch table ─────────────────────────────────────────────

    _buildVuDispatch() {
        const d = this._dispatch;
        d[Op.VSET_IMM16] = (instr) => this._hVsetImm16(instr);
        d[Op.VSET_GPR] = (instr) => this._hVsetGpr(instr);
        d[Op.VSET_MEM] = (instr) => this._hVsetMem(instr);
        d[Op.VSET_MEMI] = (instr) => this._hVsetMemi(instr);
        d[Op.VFSTAT] = (instr) => this._hVfstat(instr);
        d[Op.VFCLR] = (instr) => this._hVfclr(instr);
        d[Op.VWAIT] = (instr) => this._hVwait(instr);
        for (const opVal of VU_ASYNC_OPS) {
            d[opVal] = (instr) => this._hVasync(instr, opVal);
        }
    }

    // ── VU sync handlers ──────────────────────────────────────────────

    _hVsetImm16(instr) {
        const target = instr.operands[0];
        if (target > 4) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        const val = (instr.operands[2] << 8) | instr.operands[1];
        this.vu.regs.writeReg(target, val);
        this.regs.ip += instr.size;
    }

    _hVsetGpr(instr) {
        const target = instr.operands[0];
        if (target > 4) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        const packed = instr.operands[1];
        let val;
        if (packed & 0x10) {
            val = this.regs.read(packed & 3);
        } else {
            const rH = (packed >> 2) & 3;
            const rL = packed & 3;
            val = (this.regs.read(rH) << 8) | this.regs.read(rL);
        }
        this.vu.regs.writeReg(target, val);
        this.regs.ip += instr.size;
    }

    _hVsetMem(instr) {
        const target = instr.operands[0];
        if (target > 4) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        const addr = instr.operands[1];
        if (addr + 1 > 255) throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
        const ea = this._directAddr(addr);
        const val = this.mem.get(ea) | (this.mem.get(ea + 1) << 8);
        this.vu.regs.writeReg(target, val);
        this.regs.ip += instr.size;
    }

    _hVsetMemi(instr) {
        const target = instr.operands[0];
        if (target > 4) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        const ea = this._indirectAddr(instr.operands[1]);
        const pageOff = ea % PAGE_SIZE;
        if (pageOff + 1 >= PAGE_SIZE) {
            throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
        }
        const val = this.mem.get(ea) | (this.mem.get(ea + 1) << 8);
        this.vu.regs.writeReg(target, val);
        this.regs.ip += instr.size;
    }

    _hVfstat(instr) {
        const gpr = instr.operands[0];
        if (gpr > 3) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
        this.regs.write(gpr, this.vu.regs.vfpsr);
        this.regs.ip += instr.size;
    }

    _hVfclr(instr) {
        this.vu.regs.vfpsr = 0;
        this.regs.ip += instr.size;
    }

    _hVwait(instr) {
        if (!this.vu.isEmpty) {
            this._vuWaiting = true;
            this._vwaitSize = instr.size;
        } else {
            this.regs.ip += instr.size;
        }
    }

    // ── VU async handler ──────────────────────────────────────────────

    _hVasync(instr, opcode) {
        const vu = this.vu;
        const [fmt, mode, cond] = decodeVfm(instr.operands[0]);
        const [dstCode, s1Code, s2Code] = decodeVuRegs(instr.operands[1]);

        this._validateVfm(opcode, fmt, mode, cond, instr.operands[1]);

        if (vu.regs.vl === 0) {
            this.regs.ip += instr.size;
            return;
        }

        const elemSize = VU_FMT_ELEM_SIZE[fmt] || 1;

        // Build immediate value
        let imm = 0;
        if (mode === VU_MODE_VI) {
            for (let i = 2; i < instr.operands.length; i++) {
                imm |= instr.operands[i] << (8 * (i - 2));
            }
        } else if (mode === VU_MODE_VS) {
            imm = this.regs.read(s2Code);
        }

        // Build command with snapshotted pointers
        const cmd = new VuCommand(
            opcode,
            fmt,
            mode,
            cond,
            vu.regs.readPtr(dstCode),
            vu.regs.readPtr(s1Code),
            mode !== VU_MODE_VS ? vu.regs.readPtr(s2Code) : 0,
            vu.regs.vm,
            vu.regs.vl,
            imm,
            this._instrDef[opcode]?.mnemonic ?? "V??",
            dstCode,
            s1Code,
            s2Code,
        );

        // Auto-increment VU pointers
        this._vuAutoInc(vu, opcode, mode, dstCode, s1Code, s2Code, vu.regs.vl, elemSize);

        // If queue is full, drain until there is space
        while (vu.isFull) {
            vu.tick(this.mem, this._vuRoundingMode());
        }
        vu.enqueue(cmd);
        this.regs.ip += instr.size;
    }

    _validateVfm(opcode, fmt, mode, cond, regsByte) {
        if (fmt > 6) {
            throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        }
        if (opcode !== Op.VCMP && cond !== 0) {
            throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        }
        if (opcode === Op.VCMP && cond > 5) {
            throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        }
        if (VU_INT_FMTS.has(fmt) && (opcode === Op.VDOT || opcode === Op.VSQRT)) {
            throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        }
        // GPR broadcast restricted to byte formats (elem_size == 1)
        if (mode === VU_MODE_VS && (VU_FMT_ELEM_SIZE[fmt] || 1) > 1) {
            throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        }
        if (!this._vuValidMode(opcode, mode)) {
            throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        }
        // Reserved bits in regs byte
        if (regsByte & 0x03) {
            throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
        }
    }

    _vuValidMode(opcode, mode) {
        if (VU_VV_ONLY_OPS.has(opcode)) return mode === 0;
        if (VU_UNARY_OPS.has(opcode)) return mode === 0;
        if (opcode === Op.VMOV) return mode === 0 || mode === VU_MODE_VI;
        if (opcode === Op.VFILL) return mode === VU_MODE_VI;
        return true;
    }

    _vuAutoInc(vu, op, mode, dstCode, s1Code, s2Code, vl, sz) {
        const [dstInc, s1Inc, s2Inc] = this._vuComputeIncrements(op, mode, vl, sz);
        const increments = {};
        for (const [code, inc] of [
            [dstCode, dstInc],
            [s1Code, s1Inc],
            [s2Code, s2Inc],
        ]) {
            if (inc > 0) {
                increments[code] = Math.max(increments[code] || 0, inc);
            }
        }
        for (const code of Object.keys(increments)) {
            vu.regs.incPtr(Number(code), increments[code]);
        }
    }

    static _NO_S2_OPS = new Set([Op.VSQRT, Op.VNEG, Op.VABS, Op.VMOV, Op.VFILL]);

    _vuComputeIncrements(op, mode, vl, sz) {
        const bigS = vl * sz;
        const smallS = sz;

        // dst
        let dstInc;
        if (op === Op.VDOT) dstInc = smallS;
        else if (op === Op.VCMP) dstInc = vl;
        else if (mode === VU_MODE_R) dstInc = smallS;
        else dstInc = bigS;

        // src1
        const s1Inc = op === Op.VFILL || op === Op.VSEL ? 0 : bigS;

        // src2
        let s2Inc;
        if (CPU._NO_S2_OPS.has(op)) s2Inc = 0;
        else if (mode === VU_MODE_VS || mode === VU_MODE_VI || mode === VU_MODE_R) s2Inc = 0;
        else s2Inc = bigS;

        return [dstInc, s1Inc, s2Inc];
    }
}
