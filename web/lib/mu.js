/**
 * Matrix Unit state: registers, command queue.
 * Pure logic -- no DOM dependencies.
 */

export const MU_QUEUE_DEPTH = 4;

const MEM_SIZE = 65536;

const _PTR_NAMES = ["ma", "mb", "mc"];
const _REG_NAMES = ["ma", "mb", "mc", "mm", "mn", "mk"];

export class MuCommand {
    constructor(op, fmt, aCol, bCol, cCol, accumulate, aAddr, bAddr, cAddr, m, n, k) {
        this.op = op;
        this.fmt = fmt;
        this.aCol = aCol;
        this.bCol = bCol;
        this.cCol = cCol;
        this.accumulate = accumulate;
        this.aAddr = aAddr;
        this.bAddr = bAddr;
        this.cAddr = cAddr;
        this.m = m;
        this.n = n;
        this.k = k;
    }
}

export class MuRegisters {
    constructor() {
        this.ma = 0;
        this.mb = 0;
        this.mc = 0;
        this.mm = 0;
        this.mn = 0;
        this.mk = 0;
        this.mfpsr = 0;
    }

    readPtr(code) {
        return this[_PTR_NAMES[code]];
    }

    writeReg(code, val) {
        this[_REG_NAMES[code]] = val & 0xffff;
    }

    incPtr(code, amount) {
        this.writeReg(code, (this.readPtr(code) + amount) % MEM_SIZE);
    }

    reset() {
        this.ma = this.mb = this.mc = 0;
        this.mm = this.mn = this.mk = 0;
        this.mfpsr = 0;
    }
}

export class MuQueue {
    constructor() {
        this._q = [];
        this.fault = 0;
    }

    get isEmpty() {
        return this._q.length === 0;
    }

    get isFull() {
        return this._q.length >= MU_QUEUE_DEPTH;
    }

    peek() {
        return this._q[0];
    }

    enqueue(cmd) {
        if (this.isFull) throw new Error("MU queue full");
        this._q.push(cmd);
    }

    dequeue() {
        return this._q.shift();
    }

    flush() {
        this._q = [];
    }

    reset() {
        this._q = [];
        this.fault = 0;
    }
}
