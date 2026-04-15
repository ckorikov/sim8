/**
 * Vector Unit instruction handlers for the CPU.
 * Exported as a plain object; applied to CPU.prototype in core.js.
 */

import { VuCommand } from "./vu.js";

import {
    Op,
    CpuFault,
    ErrorCode,
    PAGE_SIZE,
    VU_ASYNC_OPS,
    VU_UNARY_OPS,
    VU_VV_ONLY_OPS,
    VU_INT_FMTS,
    VU_FMT_ELEM_SIZE,
    VU_MODE_VV,
    VU_MODE_VS,
    VU_MODE_VI,
    VU_MODE_R,
    decodeVfm,
    decodeVuRegs,
} from "./core-types.js";

// ── VU static helpers (module-level) ───────────────────────────────

const _NO_S2_OPS = new Set([Op.VSQRT, Op.VNEG, Op.VABS, Op.VMOV, Op.VFILL, Op.VGATHER, Op.VSCATTER]);

/** Destination auto-increment: reduction/dot writes one element, others write the full vector. */
function _vuDstInc(op, mode, vl, sz) {
    if (op === Op.VDOT) return sz;
    if (op === Op.VCMP) return vl;
    if (op === Op.VGATHER) return 0; // data-dependent, user must VSET
    if (mode === VU_MODE_R) return sz;
    return vl * sz;
}

/** Source-1 auto-increment: zero for VFILL/VSEL (no src1 consumed), else full vector. */
function _vuS1Inc(op, vl, sz) {
    if (op === Op.VFILL || op === Op.VSEL) return 0;
    if (op === Op.VSCATTER) return 0; // data-dependent, user must VSET
    return vl * sz;
}

/** Source-2 auto-increment: zero for unary ops, scalar/imm modes, or reduce; else full vector. */
function _vuS2Inc(op, mode, vl, sz) {
    if (_NO_S2_OPS.has(op)) return 0;
    if (mode === VU_MODE_VS || mode === VU_MODE_VI || mode === VU_MODE_R) return 0;
    return vl * sz;
}

// ── VU helpers ──────────────────────────────────────────────────────

function _vuRoundingMode() {
    const fpu = this.regs.fpu;
    return fpu !== null ? fpu.roundingMode : 0;
}

function _getVuRegs() {
    return this.vu !== null ? this.vu.regs : null;
}

function _getVuState() {
    return this.vu !== null ? this.vu.state : null;
}

function _getVuQueueItems() {
    return this.vu !== null ? this.vu.queueItems : [];
}

// ── VU dispatch table ───────────────────────────────────────────────

function _buildVuDispatch() {
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

// ── VU sync helpers ─────────────────────────────────────────────────

function _validateVuTarget(target) {
    if (target > 4) throw new CpuFault(ErrorCode.INVALID_REG, this.regs.ip);
}

function _vuReadMem16(ea) {
    return this.mem.get(ea) | (this.mem.get(ea + 1) << 8);
}

/** Decode VSET_GPR packed byte: single GPR (bit4=1) or high:low pair. */
function _decodeVsetGprPacked(packed) {
    if (packed & 0x10) return this.regs.read(packed & 3);
    return (this.regs.read((packed >> 2) & 3) << 8) | this.regs.read(packed & 3);
}

// ── VU sync handlers ────────────────────────────────────────────────

/** Validate VU target register and write value, then advance IP. */
function _vuSetReg(instr, value) {
    const target = instr.operands[0];
    this._validateVuTarget(target);
    this.vu.regs.writeReg(target, value);
    this.regs.ip += instr.size;
}

function _hVsetImm16(instr) {
    this._vuSetReg(instr, (instr.operands[2] << 8) | instr.operands[1]);
}

function _hVsetGpr(instr) {
    this._vuSetReg(instr, this._decodeVsetGprPacked(instr.operands[1]));
}

function _hVsetMem(instr) {
    const addr = instr.operands[1];
    if (addr + 2 > PAGE_SIZE) throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
    this._vuSetReg(instr, this._vuReadMem16(this._directAddr(addr)));
}

function _hVsetMemi(instr) {
    const ea = this._indirectAddr(instr.operands[1]);
    if ((ea % PAGE_SIZE) + 2 > PAGE_SIZE) throw new CpuFault(ErrorCode.PAGE_BOUNDARY, this.regs.ip);
    this._vuSetReg(instr, this._vuReadMem16(ea));
}

function _hVfstat(instr) {
    this._fpStoreToGpr(instr, this.vu.regs.vfpsr);
}

function _hVfclr(instr) {
    this.vu.regs.vfpsr = 0;
    this.regs.ip += instr.size;
}

function _hVwait(instr) {
    if (!this.vu.isEmpty) {
        this._vuWaiting = true;
        this._vwaitSize = instr.size;
    } else {
        this.regs.ip += instr.size;
    }
}

// ── VU async handler ────────────────────────────────────────────────

function _hVasync(instr, opcode) {
    const vu = this.vu;
    const [fmt, mode, cond] = decodeVfm(instr.operands[0]);
    const [dstCode, s1Code, s2Code] = decodeVuRegs(instr.operands[1]);

    this._validateVfm(opcode, fmt, mode, cond, instr.operands[1]);

    if (vu.regs.vl === 0) {
        this.regs.ip += instr.size;
        return;
    }

    const elemSize = VU_FMT_ELEM_SIZE[fmt] || 1;
    const cmd = this._vuBuildCommand(vu, opcode, fmt, mode, cond, dstCode, s1Code, s2Code, instr);
    this._vuAutoInc(vu, opcode, mode, dstCode, s1Code, s2Code, vu.regs.vl, elemSize);
    this._vuDrainAndEnqueue(vu, cmd);
    this.regs.ip += instr.size;
}

/** Build a VuCommand with snapshotted pointer values. */
function _vuBuildCommand(vu, opcode, fmt, mode, cond, dstCode, s1Code, s2Code, instr) {
    const imm = this._vuBuildImm(mode, s2Code, instr.operands);
    return new VuCommand(
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
}

/** Drain the VU queue until space is available, then enqueue cmd. */
function _vuDrainAndEnqueue(vu, cmd) {
    while (vu.isFull) {
        vu.tick(this.mem, this._vuRoundingMode());
    }
    vu.enqueue(cmd);
}

/** Return the immediate value for a VU instruction based on its addressing mode. */
function _vuBuildImm(mode, s2Code, operands) {
    if (mode === VU_MODE_VI) {
        // operands: [opcode, vfm_enc|regs, imm_byte_0, imm_byte_1, ...]
        let imm = 0;
        for (let i = 2; i < operands.length; i++) imm |= operands[i] << (8 * (i - 2));
        return imm;
    }
    if (mode === VU_MODE_VS) return this.regs.read(s2Code);
    return 0;
}

function _validateVfm(opcode, fmt, mode, cond, regsByte) {
    const fault = () => {
        throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
    };
    if (fmt > 6) fault();
    if (opcode !== Op.VCMP && cond !== 0) fault();
    if (opcode === Op.VCMP && cond > 5) fault();
    if (VU_INT_FMTS.has(fmt) && (opcode === Op.VDOT || opcode === Op.VSQRT)) fault();
    // GPR broadcast restricted to byte formats (elem_size == 1)
    if (mode === VU_MODE_VS && (VU_FMT_ELEM_SIZE[fmt] || 1) > 1) fault();
    if (!this._vuValidMode(opcode, mode)) fault();
    // Reserved bits in regs byte
    if (regsByte & 0x03) fault();
}

function _vuValidMode(opcode, mode) {
    if (VU_VV_ONLY_OPS.has(opcode)) return mode === VU_MODE_VV;
    if (VU_UNARY_OPS.has(opcode)) return mode === VU_MODE_VV;
    if (opcode === Op.VMOV) return mode === VU_MODE_VV || mode === VU_MODE_VI;
    if (opcode === Op.VFILL) return mode === VU_MODE_VI;
    return true;
}

function _vuAutoInc(vu, op, mode, dstCode, s1Code, s2Code, vl, sz) {
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
    // VGATHER/VSCATTER: VM does NOT advance (mask is reusable pattern)
    for (const code of Object.keys(increments)) {
        vu.regs.incPtr(Number(code), increments[code]);
    }
}

function _vuComputeIncrements(op, mode, vl, sz) {
    return [_vuDstInc(op, mode, vl, sz), _vuS1Inc(op, vl, sz), _vuS2Inc(op, mode, vl, sz)];
}

export const vuHandlers = {
    get vuRegs() {
        return _getVuRegs.call(this);
    },
    get vuState() {
        return _getVuState.call(this);
    },
    get vuQueueItems() {
        return _getVuQueueItems.call(this);
    },
    _vuRoundingMode,
    _buildVuDispatch,
    _validateVuTarget,
    _vuReadMem16,
    _decodeVsetGprPacked,
    _vuSetReg,
    _hVsetImm16,
    _hVsetGpr,
    _hVsetMem,
    _hVsetMemi,
    _hVfstat,
    _hVfclr,
    _hVwait,
    _hVasync,
    _vuBuildCommand,
    _vuDrainAndEnqueue,
    _vuBuildImm,
    _validateVfm,
    _vuValidMode,
    _vuAutoInc,
    _vuComputeIncrements,
};
