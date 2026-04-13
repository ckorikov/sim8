/**
 * Floating-point instruction handlers for the CPU.
 * Exported as a plain object; applied to CPU.prototype in core.js.
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

import {
    Op,
    CpuFault,
    ErrorCode,
    PAGE_SIZE,
    validateFpm,
    decodeFpm,
    FP_FMT_WIDTH,
    FP_FMT_H,
    FP_FMT_BF,
    FP_FMT_O3,
    FP_FMT_O2,
    intFromBytesLE,
    intToBytesLE,
} from "./core-types.js";

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

// ── FPU access ──────────────────────────────────────────────────────

function _getFpu() {
    const fpu = this.regs.fpu;
    if (fpu === null) {
        throw new Error("FPU not available (arch < 2)");
    }
    return fpu;
}

function _validateFpm(fpm) {
    if (!validateFpm(fpm)) {
        throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
    }
    return decodeFpm(fpm);
}

// ── FP memory helpers ───────────────────────────────────────────────

function _fpCheckMemBounds(addr, fmt) {
    const nbytes = FP_FMT_WIDTH[fmt] / 8;
    if ((addr % PAGE_SIZE) + nbytes > PAGE_SIZE) throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
    return nbytes;
}

function _fpReadMemRaw(addr, fmt) {
    const nbytes = this._fpCheckMemBounds(addr, fmt);
    const data = new Uint8Array(nbytes);
    for (let i = 0; i < nbytes; i++) data[i] = this.mem.get(addr + i);
    return data;
}

function _fpReadMem(addr, fmt) {
    return bytesToFloat(this._fpReadMemRaw(addr, fmt), fmt);
}

function _fpWriteMemRaw(addr, fmt, data) {
    this._fpCheckMemBounds(addr, fmt);
    for (let i = 0; i < data.length; i++) this.mem.set(addr + i, data[i]);
}

// ── FP register helpers ─────────────────────────────────────────────

function _fpReadReg(pos, fmt, phys = 0) {
    const raw = this._fpu.readBits(pos, fmt, phys);
    const width = FP_FMT_WIDTH[fmt];
    const data = intToBytesLE(raw, width / 8);
    return bytesToFloat(data, fmt);
}

function _fpWriteReg(pos, fmt, value, phys = 0) {
    const { data, exc } = floatToBytes(value, fmt, this._fpu.roundingMode);
    this._fpu.accumulateExceptions(exc);
    const raw = intFromBytesLE(data);
    this._fpu.writeBits(pos, fmt, raw, phys);
}

// ── FP dispatch table ───────────────────────────────────────────────

function _buildFpDispatch() {
    const d = this._dispatch;

    // -- FMOV load/store (128-131) --
    for (const [op, method, resolveAddr] of [
        [Op.FMOV_FP_ADDR, "_fpLoadRaw", (i) => this._directAddr(i.operands[1])],
        [Op.FMOV_FP_REGADDR, "_fpLoadRaw", (i) => this._indirectAddr(i.operands[1])],
        [Op.FMOV_ADDR_FP, "_fpStoreRaw", (i) => this._directAddr(i.operands[1])],
        [Op.FMOV_REGADDR_FP, "_fpStoreRaw", (i) => this._indirectAddr(i.operands[1])],
    ]) {
        d[op] = (instr) => this[method](instr, resolveAddr(instr));
    }

    // -- FMOV immediate (161-162) --
    d[Op.FMOV_FP_IMM8] = (instr) => this._hFpWriteImm8(instr);
    d[Op.FMOV_FP_IMM16] = (instr) => this._hFpWriteImm16(instr);

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
    d[Op.FABS_FP] = (instr) => this._hFpAbs(instr);
    d[Op.FNEG_FP] = (instr) => this._hFpNeg(instr);
    d[Op.FSQRT_FP] = (instr) => this._hFpSqrt(instr);

    // -- FMOV reg-reg (145) --
    d[Op.FMOV_RR] = (instr) => this._hFpCopyReg(instr);

    // -- FCVT (146) --
    d[Op.FCVT_FP_FP] = (instr) => this._hFpConvertFormat(instr);

    // -- FITOF (147) --
    d[Op.FITOF_FP_GPR] = (instr) => this._hFpIntToFloat(instr);

    // -- FFTOI (148) --
    d[Op.FFTOI_GPR_FP] = (instr) => this._hFpFloatToInt(instr);

    // -- FSTAT (149) --
    d[Op.FSTAT_GPR] = (instr) => this._hFpReadStatus(instr);

    // -- FCFG (150) --
    d[Op.FCFG_GPR] = (instr) => this._hFpReadConfig(instr);

    // -- FSCFG (151) --
    d[Op.FSCFG_GPR] = (instr) => this._hFpWriteConfig(instr);

    // -- FCLR (152) --
    d[Op.FCLR] = (instr) => this._hFpClearStatus(instr);

    // -- Reg-reg arith (153-156) --
    d[Op.FADD_RR] = this._makeFpArithRR(fpAdd);
    d[Op.FSUB_RR] = this._makeFpArithRR(fpSub);
    d[Op.FMUL_RR] = this._makeFpArithRR(fpMul);
    d[Op.FDIV_RR] = this._makeFpArithRR(fpDiv);

    // -- FCMP_RR (157) --
    d[Op.FCMP_RR] = (instr) => this._hFpCmpRegReg(instr);

    // -- FCLASS (158) --
    d[Op.FCLASS_GPR_FP] = (instr) => this._hFpClassify(instr);

    // -- FMADD (159-160) --
    d[Op.FMADD_FP_FP_ADDR] = (instr) => this._hFpMaddDirect(instr);
    d[Op.FMADD_FP_FP_REGADDR] = (instr) => this._hFpMaddIndirect(instr);
}

// ── FP handler factories ────────────────────────────────────────────

/** Apply FP binary op against a memory operand: accumulate exc, write reg back. */
function _fpApplyArithMem(instr, arithFn, addr) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    const { result, exc } = arithFn(
        this._fpReadReg(pos, fmt, phys),
        this._fpReadMem(addr, fmt),
        fmt,
        this._fpu.roundingMode,
    );
    this._fpu.accumulateExceptions(exc);
    this._fpWriteReg(pos, fmt, result, phys);
    this.regs.ip += instr.size;
}

/** FP compare against a memory operand: accumulate exc, update Z and C. */
function _fpApplyCmpMem(instr, addr) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    this._fpApplyCmp(this._fpReadReg(pos, fmt, phys), this._fpReadMem(addr, fmt));
    this.regs.ip += instr.size;
}

function _makeFpArithMem(arithFn, resolveAddr) {
    return (instr) => this._fpApplyArithMem(instr, arithFn, resolveAddr(instr.operands[1]));
}

function _makeFpCmpMem(resolveAddr) {
    return (instr) => this._fpApplyCmpMem(instr, resolveAddr(instr.operands[1]));
}

/** Apply a binary FP op to two FP regs with matching format: accumulate exc, write dst back. */
function _fpApplyRegBinary(instr, arithFn) {
    const [dstPhys, dstPos, dstFmt, srcPhys, srcPos, srcFmt] = this._validateTwoFpmSameFmt(
        instr.operands[0],
        instr.operands[1],
    );
    const { result, exc } = arithFn(
        this._fpReadReg(dstPos, dstFmt, dstPhys),
        this._fpReadReg(srcPos, srcFmt, srcPhys),
        dstFmt,
        this._fpu.roundingMode,
    );
    this._fpu.accumulateExceptions(exc);
    this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
    this.regs.ip += instr.size;
}

function _makeFpArithRR(arithFn) {
    return (instr) => this._fpApplyRegBinary(instr, arithFn);
}

// ── FP individual handlers ──────────────────────────────────────────

function _fpLoadRaw(instr, addr) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    const data = this._fpReadMemRaw(addr, fmt);
    const raw = intFromBytesLE(data);
    this._fpu.writeBits(pos, fmt, raw, phys);
    this.regs.ip += instr.size;
}

function _fpStoreRaw(instr, addr) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    const raw = this._fpu.readBits(pos, fmt, phys);
    const data = intToBytesLE(raw, FP_FMT_WIDTH[fmt] / 8);
    this._fpWriteMemRaw(addr, fmt, data);
    this.regs.ip += instr.size;
}

/** Read FP register, apply unary fn(val, fmt, rm), accumulate exc, write back. */
function _fpApplyRegUnary(instr, fn) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    const { result, exc } = fn(this._fpReadReg(pos, fmt, phys), fmt, this._fpu.roundingMode);
    this._fpu.accumulateExceptions(exc);
    this._fpWriteReg(pos, fmt, result, phys);
    this.regs.ip += instr.size;
}

function _fpApplyBitwiseUnary(instr, fn) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    const raw = this._fpu.readBits(pos, fmt, phys);
    const result = fn(raw, FP_FMT_WIDTH[fmt]);
    this._fpu.writeBits(pos, fmt, result, phys);
    this.regs.ip += instr.size;
}

// -- FMOV immediate (161-162): raw bit write, no rounding --

/** Write raw bits to FP register; throw FP_FORMAT fault if fmt not in validFmts. */
function _fpWriteImm(instr, rawBits, validFmts) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    if (!validFmts.includes(fmt)) throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
    this._fpu.writeBits(pos, fmt, rawBits, phys);
    this.regs.ip += instr.size;
}

function _hFpWriteImm8(instr) {
    this._fpWriteImm(instr, instr.operands[1], [FP_FMT_O3, FP_FMT_O2]);
}

function _hFpWriteImm16(instr) {
    this._fpWriteImm(instr, instr.operands[1] | (instr.operands[2] << 8), [FP_FMT_H, FP_FMT_BF]);
}

// -- FABS (142) / FNEG (143) --

function _hFpAbs(instr) {
    this._fpApplyBitwiseUnary(instr, fpAbs);
}

function _hFpNeg(instr) {
    this._fpApplyBitwiseUnary(instr, fpNeg);
}

// -- FSQRT (144) --

function _hFpSqrt(instr) {
    this._fpApplyRegUnary(instr, fpSqrt);
}

// -- FMOV reg-reg (145): raw copy, no rounding --

function _hFpCopyReg(instr) {
    const [dstPhys, dstPos, dstFmt, srcPhys, srcPos, srcFmt] = this._validateTwoFpmSameFmt(
        instr.operands[0],
        instr.operands[1],
    );
    this._fpu.writeBits(dstPos, dstFmt, this._fpu.readBits(srcPos, srcFmt, srcPhys), dstPhys);
    this.regs.ip += instr.size;
}

// -- FCVT (146): convert between FP formats --

function _hFpConvertFormat(instr) {
    const [dstPhys, dstPos, dstFmt] = this._validateFpm(instr.operands[0]);
    const [srcPhys, srcPos, srcFmt] = this._validateFpm(instr.operands[1]);
    this._fpWriteReg(dstPos, dstFmt, this._fpReadReg(srcPos, srcFmt, srcPhys), dstPhys);
    this.regs.ip += instr.size;
}

// -- FITOF (147): int → FP --

function _hFpIntToFloat(instr) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    this._fpWriteReg(pos, fmt, this.regs.read(this._decodeGpr(instr.operands[1])), phys);
    this.regs.ip += instr.size;
}

// -- FFTOI (148): FP → uint8 with saturation --

/** Convert float to uint8 with saturation. Returns {result, exc}. */
function _fpFloatToUint8Saturated(fpVal) {
    const excInvalid = { invalid: true, divZero: false, overflow: false, underflow: false, inexact: false };
    if (Number.isNaN(fpVal)) return { result: 0, exc: excInvalid };
    if (!Number.isFinite(fpVal)) return { result: fpVal > 0 ? 255 : 0, exc: excInvalid };
    const rounded = _ROUND_FNS[this._fpu.roundingMode](fpVal);
    return {
        result: Math.max(0, Math.min(255, rounded)),
        exc: { invalid: false, divZero: false, overflow: false, underflow: false, inexact: rounded !== fpVal },
    };
}

function _hFpFloatToInt(instr) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    const gpr = this._decodeGpr(instr.operands[1]);
    const { result, exc } = this._fpFloatToUint8Saturated(this._fpReadReg(pos, fmt, phys));
    this._fpu.accumulateExceptions(exc);
    this.regs.write(gpr, result);
    this.regs.ip += instr.size;
}

// -- FSTAT/FCFG/FSCFG/FCLR (149-152) --

/** Write value to GPR encoded in operands[0], then advance IP. */
function _fpStoreToGpr(instr, value) {
    this.regs.write(this._decodeGpr(instr.operands[0]), value);
    this.regs.ip += instr.size;
}

function _hFpReadStatus(instr) {
    this._fpStoreToGpr(instr, this._fpu.fpsr);
}
function _hFpReadConfig(instr) {
    this._fpStoreToGpr(instr, this._fpu.fpcr);
}

function _hFpWriteConfig(instr) {
    this._fpu.fpcr = this.regs.read(this._decodeGpr(instr.operands[0])) & 0x03;
    this.regs.ip += instr.size;
}

function _hFpClearStatus(instr) {
    this._fpu.fpsr = 0;
    this.regs.ip += instr.size;
}

// -- FCMP_RR (157) --

function _hFpCmpRegReg(instr) {
    const [dstPhys, dstPos, dstFmt, srcPhys, srcPos, srcFmt] = this._validateTwoFpmSameFmt(
        instr.operands[0],
        instr.operands[1],
    );
    this._fpApplyCmp(this._fpReadReg(dstPos, dstFmt, dstPhys), this._fpReadReg(srcPos, srcFmt, srcPhys));
    this.regs.ip += instr.size;
}

// -- FCLASS (158) --

function _hFpClassify(instr) {
    const [phys, pos, fmt] = this._validateFpm(instr.operands[0]);
    const gpr = this._decodeGpr(instr.operands[1]);
    const [val, raw] = this._fpReadRegAndRaw(pos, fmt, phys);
    this.regs.write(gpr, fpClassify(val, raw, FP_FMT_WIDTH[fmt], fmt));
    this.regs.ip += instr.size;
}

function _fpMergeExc(exc1, exc2) {
    return {
        invalid: exc1.invalid || exc2.invalid,
        divZero: exc1.divZero || exc2.divZero,
        overflow: exc1.overflow || exc2.overflow,
        underflow: exc1.underflow || exc2.underflow,
        inexact: exc1.inexact || exc2.inexact,
    };
}

/** FP compare: accumulate exceptions, update Z and C flags. */
function _fpApplyCmp(a, b) {
    const { zero, carry, exc } = fpCmp(a, b);
    this._fpu.accumulateExceptions(exc);
    this.regs.flags.z = zero;
    this.regs.flags.c = carry;
}

/** Read FP register, returning [float_value, raw_bits]. */
function _fpReadRegAndRaw(pos, fmt, phys) {
    const raw = this._fpu.readBits(pos, fmt, phys);
    return [bytesToFloat(intToBytesLE(raw, FP_FMT_WIDTH[fmt] / 8), fmt), raw];
}

/** Validate two FPM operands requiring matching format. Returns [dstPhys, dstPos, dstFmt, srcPhys, srcPos, srcFmt]. */
function _validateTwoFpmSameFmt(op0, op1) {
    const [dstPhys, dstPos, dstFmt] = this._validateFpm(op0);
    const [srcPhys, srcPos, srcFmt] = this._validateFpm(op1);
    if (dstFmt !== srcFmt) throw new CpuFault(ErrorCode.FP_FORMAT, this.regs.ip);
    return [dstPhys, dstPos, dstFmt, srcPhys, srcPos, srcFmt];
}

function _fpDoMadd(instr, addr) {
    const [dstPhys, dstPos, dstFmt, srcPhys, srcPos, srcFmt] = this._validateTwoFpmSameFmt(
        instr.operands[0],
        instr.operands[1],
    );

    const rm = this._fpu.roundingMode;
    const { result: mulResult, exc: mulExc } = fpMul(
        this._fpReadReg(srcPos, srcFmt, srcPhys),
        this._fpReadMem(addr, dstFmt),
        dstFmt,
        rm,
    );
    const { result, exc: addExc } = fpAdd(mulResult, this._fpReadReg(dstPos, dstFmt, dstPhys), dstFmt, rm);
    this._fpu.accumulateExceptions(this._fpMergeExc(mulExc, addExc));
    this._fpWriteReg(dstPos, dstFmt, result, dstPhys);
    this.regs.ip += instr.size;
}

// -- FMADD (159-160) --

function _hFpMaddDirect(instr) {
    this._fpDoMadd(instr, this._directAddr(instr.operands[2]));
}

function _hFpMaddIndirect(instr) {
    this._fpDoMadd(instr, this._indirectAddr(instr.operands[2]));
}

export const fpHandlers = {
    get _fpu() {
        return _getFpu.call(this);
    },
    _validateFpm,
    _fpCheckMemBounds,
    _fpReadMemRaw,
    _fpReadMem,
    _fpWriteMemRaw,
    _fpReadReg,
    _fpWriteReg,
    _buildFpDispatch,
    _fpApplyArithMem,
    _fpApplyCmpMem,
    _makeFpArithMem,
    _makeFpCmpMem,
    _fpApplyRegBinary,
    _makeFpArithRR,
    _fpLoadRaw,
    _fpStoreRaw,
    _fpApplyRegUnary,
    _fpApplyBitwiseUnary,
    _fpWriteImm,
    _hFpWriteImm8,
    _hFpWriteImm16,
    _hFpAbs,
    _hFpNeg,
    _hFpSqrt,
    _hFpCopyReg,
    _hFpConvertFormat,
    _hFpIntToFloat,
    _fpFloatToUint8Saturated,
    _hFpFloatToInt,
    _fpStoreToGpr,
    _hFpReadStatus,
    _hFpReadConfig,
    _hFpWriteConfig,
    _hFpClearStatus,
    _hFpCmpRegReg,
    _hFpClassify,
    _fpMergeExc,
    _fpApplyCmp,
    _fpReadRegAndRaw,
    _validateTwoFpmSameFmt,
    _fpDoMadd,
    _hFpMaddDirect,
    _hFpMaddIndirect,
};
