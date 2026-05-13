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
    VU_FP_ONLY_OPS,
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

const _NO_S2_OPS = new Set([Op.VSQRT, Op.VEXP, Op.VNEG, Op.VABS, Op.VMOV, Op.VGATHER, Op.VSCATTER]);
const _NO_R_OPS = new Set([Op.VFMADD]);

/** Destination auto-increment: reduction/dot writes one element, others write the full vector. */
function _vuDstInc(op, mode, vl, sz) {
    if (op === Op.VDOT) return sz;
    if (op === Op.VCMP) return vl;
    if (op === Op.VGATHER) return 0; // data-dependent, user must VSET
    if (mode === VU_MODE_R) return sz;
    return vl * sz;
}

/** Source-1 auto-increment.
 * Zero when src1 is not consumed (VSEL alt-pointer, VSCATTER data-dependent,
 * VMOV vs/vi where source is mem[s2_ptr] / imm). */
function _vuS1Inc(op, mode, vl, sz) {
    if (op === Op.VSEL || op === Op.VSCATTER) return 0;
    if (op === Op.VMOV && (mode === VU_MODE_VS || mode === VU_MODE_VI)) return 0;
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
    return this.regs.fpu?.roundingMode ?? 0;
}

function _getVuRegs() {
    return this.vu?.regs ?? null;
}

function _getVuState() {
    return this.vu?.state ?? null;
}

function _getVuQueueItems() {
    return this.vu?.queueItems ?? [];
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
    d[Op.VCVT] = (instr) => this._hVcvt(instr);
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

// ── VCVT handler ────────────────────────────────────────────────────

function _hVcvt(instr) {
    const vu = this.vu;
    const [dstFmt, dstMode] = decodeVfm(instr.operands[0]);
    const [srcFmt] = decodeVfm(instr.operands[1]);
    const [dstCode, s1Code] = decodeVuRegs(instr.operands[2]);

    if (dstFmt > 6 || srcFmt > 6 || dstMode === VU_MODE_R) {
        throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
    }

    if (vu.regs.vl === 0) {
        this.regs.ip += instr.size;
        return;
    }

    const dstSz = VU_FMT_ELEM_SIZE[dstFmt] || 1;
    const srcSz = VU_FMT_ELEM_SIZE[srcFmt] || 1;
    const cmd = new VuCommand(
        Op.VCVT,
        dstFmt,
        VU_MODE_VV,
        0,
        vu.regs.readPtr(dstCode),
        vu.regs.readPtr(s1Code),
        0,
        vu.regs.vm,
        vu.regs.vl,
        0,
        "VCVT",
        dstCode,
        s1Code,
        0,
    );
    cmd.srcFmt = srcFmt;
    vu.regs.incPtr(dstCode, vu.regs.vl * dstSz);
    vu.regs.incPtr(s1Code, vu.regs.vl * srcSz);
    this._vuDrainAndEnqueue(vu, cmd);
    this.regs.ip += instr.size;
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
    const imm = this._vuBuildImm(mode, s2Code, instr.operands, opcode, fmt, vu, s1Code);
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

/** Return the immediate value for a VU instruction based on its addressing mode.
 * For .vs (mem-scalar broadcast), snapshot sz bytes from mem[s2_ptr] into imm. */
function _vuBuildImm(mode, s2Code, operands, _opcode, fmt, vu, _s1Code) {
    if (mode === VU_MODE_VI) {
        // operands: [vfmEnc, regs, imm_byte_0, imm_byte_1, ...]
        return operands.slice(2).reduce((acc, b, i) => acc | (b << (8 * i)), 0);
    }
    if (mode === VU_MODE_VS) {
        const sz = VU_FMT_ELEM_SIZE[fmt] || 1;
        const base = vu.regs.readPtr(s2Code);
        let imm = 0;
        for (let i = 0; i < sz; i++) imm |= this.mem.get(base + i) << (8 * i);
        return imm;
    }
    return 0;
}

function _validateVfm(opcode, fmt, mode, cond, regsByte) {
    const fault = () => {
        throw new CpuFault(ErrorCode.VU_FORMAT, this.regs.ip);
    };
    if (fmt > 6) fault();
    if (opcode !== Op.VCMP && cond !== 0) fault();
    if (opcode === Op.VCMP && cond > 5) fault();
    if (VU_INT_FMTS.has(fmt) && VU_FP_ONLY_OPS.has(opcode)) fault();
    if (!this._vuValidMode(opcode, mode)) fault();
    // Reserved bits in regs byte
    if (regsByte & 0x03) fault();
}

function _vuValidMode(opcode, mode) {
    if (VU_VV_ONLY_OPS.has(opcode) || VU_UNARY_OPS.has(opcode)) return mode === VU_MODE_VV;
    if (opcode === Op.VMOV) {
        // vv (copy), vs (mem-scalar broadcast), vi (imm broadcast). No reduction.
        return mode === VU_MODE_VV || mode === VU_MODE_VS || mode === VU_MODE_VI;
    }
    if (_NO_R_OPS.has(opcode)) return mode === VU_MODE_VV || mode === VU_MODE_VS || mode === VU_MODE_VI;
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
    return [_vuDstInc(op, mode, vl, sz), _vuS1Inc(op, mode, vl, sz), _vuS2Inc(op, mode, vl, sz)];
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
    _hVcvt,
    _hVasync,
    _vuBuildCommand,
    _vuDrainAndEnqueue,
    _vuBuildImm,
    _validateVfm,
    _vuValidMode,
    _vuAutoInc,
    _vuComputeIncrements,
};
