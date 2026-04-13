/**
 * CPU core: constructor, public API, and execution control.
 * Integer, FP, and VU instruction handlers live in core-handlers-*.js.
 * Helper types (Memory, ALU, RegisterFile, etc.) live in core-types.js.
 */

import { VectorUnit } from "./vu.js";

import {
    // ISA tables
    Op,
    ISA,
    ISA_FP,
    ISA_VU,
    // Core types
    Memory,
    RegisterFile,
    CpuFault,
    CpuState,
    ErrorCode,
    PAGE_SIZE,
    IO_START,
    SP_INIT,
    FP_FMT_WIDTH,
    decode,
} from "./core-types.js";

import { intHandlers } from "./core-handlers-int.js";
import { fpHandlers } from "./core-handlers-fp.js";
import { vuHandlers } from "./core-handlers-vu.js";

// Re-export public API from core-types so existing imports keep working
export { CpuState, ErrorCode, PAGE_SIZE, IO_START, SP_INIT, Memory };

// ── CPU ──────────────────────────────────────────────────────────────

// Cycle cost per FP format for memory-accessing FP instructions.
// Derived from FP_FMT_WIDTH (fmt 0..4): bits / 8 = bytes transferred.
const _FP_FMT_MEM_COST = Array.from({ length: 5 }, (_, fmt) => FP_FMT_WIDTH[fmt] / 8);

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
            if (!d.fmtDep) this._opCost[d.op] = d.cost;
        }
    }

    // ── Public API ────────────────────────────────────────────────────

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
        if (this._consumeVuFault()) return false;
        if (this._vuWaiting) this._stepVwait();
        return true;
    }

    /** Enter fault from pending VU fault code. Returns true if a fault was consumed. */
    _consumeVuFault() {
        if (this.vu.fault === 0) return false;
        const code = this.vu.fault;
        this.vu.fault = 0;
        this._vuWaiting = false;
        this._enterFault(code);
        return true;
    }

    /** Handle one VWAIT stall cycle: advance IP when VU queue drains. */
    _stepVwait() {
        this._cycles += 1;
        if (this.vu.isEmpty) {
            this._vuWaiting = false;
            this.regs.ip += this._vwaitSize;
            this._vwaitSize = 0;
        }
    }

    /** Fetch and decode the next instruction; enter FAULT and return null on decode error. */
    _fetchInstr() {
        try {
            return decode(this.mem, this.regs.ip, this._arch);
        } catch (e) {
            if (e instanceof CpuFault) {
                this._enterFault(e.code);
                return null;
            }
            throw e;
        }
    }

    /** Dispatch instr to its handler; enter FAULT and return false on execution error. */
    _executeInstr(instr) {
        try {
            this._dispatch[instr.op](instr);
            return true;
        } catch (e) {
            if (e instanceof CpuFault) {
                this._enterFault(e.code);
                return false;
            }
            throw e;
        }
    }

    /** Update step/cycle/memory counters after a successful instruction. */
    _updateStats(instr) {
        this._steps += 1;
        this._cycles += this._computeCost(instr);
        const used = this.mem.usedBytes();
        if (used > this._peakMem) this._peakMem = used;
    }

    _computeCost(instr) {
        const op = instr.op;
        const d = this._instrDef[op];
        if (d?.fmtDep) {
            const fmt = instr.operands[0] % 8;
            return (_FP_FMT_MEM_COST[fmt] ?? 4) + d.cost;
        }
        return this._opCost[op] ?? 1;
    }

    /** Execute one CPU instruction. Does NOT touch VU. */
    step() {
        if (this.state === CpuState.FAULT) return false;
        if (this.state === CpuState.HALTED) return false;
        if (this._vuWaiting) return false; // CPU stalled on VWAIT

        if (this.state === CpuState.IDLE) this.state = CpuState.RUNNING;

        const instr = this._fetchInstr();
        if (instr === null) return false;

        if (instr.op === Op.HLT) {
            this.state = CpuState.HALTED;
            return false;
        }

        if (!this._executeInstr(instr)) return false;
        this._updateStats(instr);
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

    // ── Fault handling ────────────────────────────────────────────────

    _enterFault(code) {
        this.regs.flags.f = true;
        this.regs.a = code;
        this.state = CpuState.FAULT;
    }
}

// Apply handler mixins to CPU.prototype.
// Object.getOwnPropertyDescriptors preserves getters (e.g. _fpu, vuRegs, vuState).
Object.defineProperties(CPU.prototype, Object.getOwnPropertyDescriptors(intHandlers));
Object.defineProperties(CPU.prototype, Object.getOwnPropertyDescriptors(fpHandlers));
Object.defineProperties(CPU.prototype, Object.getOwnPropertyDescriptors(vuHandlers));
