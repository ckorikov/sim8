/**
 * Integer / ALU instruction handlers for the CPU.
 * Exported as a plain object; applied to CPU.prototype in core.js.
 */

import { Reg, ALU, CpuFault, ErrorCode, PAGE_SIZE, SP_INIT, decodeRegaddr } from "./core-types.js";
import { DISPATCH_CONFIG } from "./_dispatch_config.js";

// ── Address resolution ──────────────────────────────────────────────

function _directAddr(offset) {
    return this.regs.dp * PAGE_SIZE + offset;
}

function _indirectAddr(encoded) {
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

// ── Register validation ─────────────────────────────────────────────

function _decodeGpr(code) {
    if (code > Reg.D) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
    }
    return code;
}

function _decodeGprOrSp(code) {
    if (code > Reg.SP) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
    }
    return code;
}

function _decodeGprOrDp(code) {
    if (code > Reg.D && code !== Reg.DP) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
    }
    return code;
}

function _decodeMovReg(code) {
    if (code > Reg.DP) {
        throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
    }
    return code;
}

// ── Source resolvers ────────────────────────────────────────────────

function _srcRegaddr(instr) {
    return this.mem.get(this._indirectAddr(instr.operands[1]));
}

function _srcAddr(instr) {
    return this.mem.get(this._directAddr(instr.operands[1]));
}

function _srcConst(instr) {
    return instr.operands[1];
}

function _srcStkReg(instr) {
    const code = this._decodeGprOrSp(instr.operands[1]);
    return this.regs.read(code);
}

function _srcGprReg(instr) {
    const code = this._decodeGpr(instr.operands[1]);
    return this.regs.read(code);
}

function _srcMuldivReg(instr) {
    const code = this._decodeGpr(instr.operands[0]);
    return this.regs.read(code);
}

function _srcMuldivRegaddr(instr) {
    return this.mem.get(this._indirectAddr(instr.operands[0]));
}

function _srcMuldivAddr(instr) {
    return this.mem.get(this._directAddr(instr.operands[0]));
}

function _srcMuldivConst(instr) {
    return instr.operands[0];
}

// ── Stack helpers ───────────────────────────────────────────────────

function _doPush(value) {
    if (this.regs.sp === 0) {
        throw new CpuFault(ErrorCode.STACK_OVERFLOW, this.regs.ip);
    }
    this.mem.set(this.regs.sp, value);
    this.regs.sp = this.regs.sp - 1;
}

function _doPop() {
    if (this.regs.sp >= SP_INIT) {
        throw new CpuFault(ErrorCode.STACK_UNDERFLOW, this.regs.ip);
    }
    this.regs.sp = this.regs.sp + 1;
    return this.mem.get(this.regs.sp);
}

function _doCall(target, returnAddr) {
    this._doPush(returnAddr);
    this.regs.ip = target;
}

// ── Unary ALU helpers ───────────────────────────────────────────────

function _applyUnaryAlu(instr, aluFn) {
    const code = this._decodeGprOrSp(instr.operands[0]);
    const [result, carry, zero] = aluFn(this.regs.read(code));
    this.regs.flags.c = carry;
    this.regs.flags.z = zero;
    this.regs.write(code, result);
    this.regs.ip += instr.size;
}

/** Apply a bitwise unary op (NOT) to a GPR: always clears C, updates Z. */
function _applyGprBitwiseUnary(instr, aluFn) {
    const code = this._decodeGpr(instr.operands[0]);
    const [result, zero] = aluFn(this.regs.read(code));
    this.regs.flags.c = false;
    this.regs.flags.z = zero;
    this.regs.write(code, result);
    this.regs.ip += instr.size;
}

// ── Handler factories ───────────────────────────────────────────────

/** Apply a 2-operand ALU op (ADD/SUB/CMP): update C and Z flags, optionally write back. */
function _applyAlu2op(instr, aluFn, resolveSrc, writeback = true) {
    const destCode = this._decodeGprOrSp(instr.operands[0]);
    const [result, carry, zero] = aluFn(this.regs.read(destCode), resolveSrc(instr));
    this.regs.flags.c = carry;
    this.regs.flags.z = zero;
    if (writeback) this.regs.write(destCode, result);
    this.regs.ip += instr.size;
}

/** Apply a 2-operand bitwise op (AND/OR/XOR): always clears C, updates Z. */
function _applyBitwise2op(instr, aluFn, resolveSrc) {
    const destCode = this._decodeGpr(instr.operands[0]);
    const [result, zero] = aluFn(this.regs.read(destCode), resolveSrc(instr));
    this.regs.flags.c = false;
    this.regs.flags.z = zero;
    this.regs.write(destCode, result);
    this.regs.ip += instr.size;
}

/** Apply a 2-operand shift (SHL/SHR): count==0 only updates Z; otherwise updates C, Z, and writes back. */
function _applyShift2op(instr, aluFn, resolveSrc) {
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
}

/** Evaluate condition and jump to target or advance IP. */
function _applyJcc(instr, condition, isReg) {
    const target = isReg ? this.regs.read(this._decodeGpr(instr.operands[0])) : instr.operands[0];
    if (condition()) {
        this.regs.ip = target;
    } else {
        this.regs.ip += instr.size;
    }
}

/** Apply MUL: A = A * operand, update C and Z. */
function _applyMuldiv(instr, aluFn, resolveSrc) {
    const [result, carry, zero] = aluFn(this.regs.a, resolveSrc(instr));
    this.regs.flags.c = carry;
    this.regs.flags.z = zero;
    this.regs.a = result;
    this.regs.ip += instr.size;
}

/** Apply DIV: A = A / operand. Throws FAULT on zero divisor. */
function _applyDiv(instr, resolveSrc) {
    const right = resolveSrc(instr);
    if (right === 0) throw new CpuFault(ErrorCode.DIV_ZERO, this.regs.ip);
    const [result, carry, zero] = ALU.div(this.regs.a, right);
    this.regs.flags.c = carry;
    this.regs.flags.z = zero;
    this.regs.a = result;
    this.regs.ip += instr.size;
}

function _makeAlu2op(aluFn, resolveSrc, writeback = true) {
    return (instr) => this._applyAlu2op(instr, aluFn, resolveSrc, writeback);
}

function _makeBitwise2op(aluFn, resolveSrc) {
    return (instr) => this._applyBitwise2op(instr, aluFn, resolveSrc);
}

function _makeShift2op(aluFn, resolveSrc) {
    return (instr) => this._applyShift2op(instr, aluFn, resolveSrc);
}

function _makeJcc(condition, isReg) {
    return (instr) => this._applyJcc(instr, condition, isReg);
}

function _makeMuldiv(aluFn, resolveSrc) {
    return (instr) => this._applyMuldiv(instr, aluFn, resolveSrc);
}

function _makeDiv(resolveSrc) {
    return (instr) => this._applyDiv(instr, resolveSrc);
}

// ── Integer handlers ────────────────────────────────────────────────

/** Load byte from memory address into destination register. */
function _movRegFromMem(instr, addr) {
    this.regs.write(this._decodeMovReg(instr.operands[0]), this.mem.get(addr));
    this.regs.ip += instr.size;
}

/** Store source register value to memory address. */
function _movMemFromReg(instr, addr) {
    this.mem.set(addr, this.regs.read(this._decodeMovReg(instr.operands[1])));
    this.regs.ip += instr.size;
}

/** Store immediate constant to memory address. */
function _movMemConst(instr, addr) {
    this.mem.set(addr, instr.operands[1]);
    this.regs.ip += instr.size;
}

function _hMovRegReg(instr) {
    this.regs.write(this._decodeMovReg(instr.operands[0]), this.regs.read(this._decodeMovReg(instr.operands[1])));
    this.regs.ip += instr.size;
}

function _hMovRegAddr(instr) {
    this._movRegFromMem(instr, this._directAddr(instr.operands[1]));
}
function _hMovRegRegaddr(instr) {
    this._movRegFromMem(instr, this._indirectAddr(instr.operands[1]));
}
function _hMovAddrReg(instr) {
    this._movMemFromReg(instr, this._directAddr(instr.operands[0]));
}
function _hMovRegaddrReg(instr) {
    this._movMemFromReg(instr, this._indirectAddr(instr.operands[0]));
}

function _hMovRegConst(instr) {
    this.regs.write(this._decodeMovReg(instr.operands[0]), instr.operands[1]);
    this.regs.ip += instr.size;
}

function _hMovAddrConst(instr) {
    this._movMemConst(instr, this._directAddr(instr.operands[0]));
}
function _hMovRegaddrConst(instr) {
    this._movMemConst(instr, this._indirectAddr(instr.operands[0]));
}

function _hInc(instr) {
    this._applyUnaryAlu(instr, ALU.inc);
}
function _hDec(instr) {
    this._applyUnaryAlu(instr, ALU.dec);
}

function _hJmpReg(instr) {
    this.regs.ip = this.regs.read(this._decodeGpr(instr.operands[0]));
}
function _hJmpAddr(instr) {
    this.regs.ip = instr.operands[0];
}

function _doPushAndAdvance(instr, value) {
    this._doPush(value);
    this.regs.ip += instr.size;
}

function _hPushReg(instr) {
    this._doPushAndAdvance(instr, this.regs.read(this._decodeGprOrDp(instr.operands[0])));
}
function _hPushRegaddr(instr) {
    this._doPushAndAdvance(instr, this.mem.get(this._indirectAddr(instr.operands[0])));
}
function _hPushAddr(instr) {
    this._doPushAndAdvance(instr, this.mem.get(this._directAddr(instr.operands[0])));
}
function _hPushConst(instr) {
    this._doPushAndAdvance(instr, instr.operands[0]);
}

function _hPopReg(instr) {
    this.regs.write(this._decodeGprOrDp(instr.operands[0]), this._doPop());
    this.regs.ip += instr.size;
}

function _hCallReg(instr) {
    this._doCall(this.regs.read(this._decodeGpr(instr.operands[0])), this.regs.ip + instr.size);
}

function _hCallAddr(instr) {
    this._doCall(instr.operands[0], this.regs.ip + instr.size);
}

function _hRet() {
    this.regs.ip = this._doPop();
}

function _hNot(instr) {
    this._applyGprBitwiseUnary(instr, ALU.not);
}

// ── Integer dispatch table ──────────────────────────────────────────

function _buildDispatch() {
    const d = this._dispatch;
    const alu = {
        add: ALU.add,
        sub: ALU.sub,
        mul: ALU.mul,
        and: ALU.and,
        or: ALU.or,
        xor: ALU.xor,
        shl: ALU.shl,
        shr: ALU.shr,
    };
    const src = {
        stkReg: (i) => this._srcStkReg(i),
        regaddr: (i) => this._srcRegaddr(i),
        addr: (i) => this._srcAddr(i),
        const: (i) => this._srcConst(i),
        gprReg: (i) => this._srcGprReg(i),
        muldivReg: (i) => this._srcMuldivReg(i),
        muldivRegaddr: (i) => this._srcMuldivRegaddr(i),
        muldivAddr: (i) => this._srcMuldivAddr(i),
        muldivConst: (i) => this._srcMuldivConst(i),
    };
    const jcc = {
        c: () => this.regs.flags.c,
        nc: () => !this.regs.flags.c,
        z: () => this.regs.flags.z,
        nz: () => !this.regs.flags.z,
        a: () => !this.regs.flags.c && !this.regs.flags.z,
        na: () => this.regs.flags.c || this.regs.flags.z,
    };
    for (const [op, type, a1, a2] of DISPATCH_CONFIG) {
        switch (type) {
            case "direct":
                d[op] = (instr) => this[a1](instr);
                break;
            case "alu_2op":
                d[op] = this._makeAlu2op(alu[a1], src[a2]);
                break;
            case "alu_2op_no_wb":
                d[op] = this._makeAlu2op(alu[a1], src[a2], false);
                break;
            case "bitwise":
                d[op] = this._makeBitwise2op(alu[a1], src[a2]);
                break;
            case "shift":
                d[op] = this._makeShift2op(alu[a1], src[a2]);
                break;
            case "muldiv":
                d[op] = this._makeMuldiv(alu[a1], src[a2]);
                break;
            case "div":
                d[op] = this._makeDiv(src[a1]);
                break;
            case "jcc":
                d[op] = this._makeJcc(jcc[a1], a2 === "reg");
                break;
        }
    }
}

export const intHandlers = {
    _directAddr,
    _indirectAddr,
    _decodeGpr,
    _decodeGprOrSp,
    _decodeGprOrDp,
    _decodeMovReg,
    _srcRegaddr,
    _srcAddr,
    _srcConst,
    _srcStkReg,
    _srcGprReg,
    _srcMuldivReg,
    _srcMuldivRegaddr,
    _srcMuldivAddr,
    _srcMuldivConst,
    _doPush,
    _doPop,
    _doCall,
    _applyUnaryAlu,
    _applyGprBitwiseUnary,
    _applyAlu2op,
    _applyBitwise2op,
    _applyShift2op,
    _applyJcc,
    _applyMuldiv,
    _applyDiv,
    _makeAlu2op,
    _makeBitwise2op,
    _makeShift2op,
    _makeJcc,
    _makeMuldiv,
    _makeDiv,
    _movRegFromMem,
    _movMemFromReg,
    _movMemConst,
    _hMovRegReg,
    _hMovRegAddr,
    _hMovRegRegaddr,
    _hMovAddrReg,
    _hMovRegaddrReg,
    _hMovRegConst,
    _hMovAddrConst,
    _hMovRegaddrConst,
    _hInc,
    _hDec,
    _hJmpReg,
    _hJmpAddr,
    _doPushAndAdvance,
    _hPushReg,
    _hPushRegaddr,
    _hPushAddr,
    _hPushConst,
    _hPopReg,
    _hCallReg,
    _hCallAddr,
    _hRet,
    _hNot,
    _buildDispatch,
};
