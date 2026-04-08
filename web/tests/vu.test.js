import { describe, it, expect, beforeEach } from "vitest";
import { CPU, CpuState } from "../lib/core.js";
import { Op, encodeVfm, encodeVuRegs } from "../lib/isa.js";

// ── Helpers ──────────────────────────────────────────────────────────

function makeCPU() {
    return new CPU({ arch: 3 });
}

/** Build VSET VL, imm16 instruction (4 bytes). */
function vsetVL(val) {
    return [Op.VSET_IMM16, 4, val & 0xff, (val >> 8) & 0xff];
}

/** Build VSET VA/VB/VC, imm16 (target: 0=VA,1=VB,2=VC). */
function vsetPtr(target, val) {
    return [Op.VSET_IMM16, target, val & 0xff, (val >> 8) & 0xff];
}

/** Build async VU instruction (3 bytes: opcode + vfm + regs). */
function vuAsync(op, fmt, mode, dst, src1, src2, cond = 0) {
    return [op, encodeVfm(fmt, mode, cond), encodeVuRegs(dst, src1, src2)];
}

/** Load program at page 0, run N steps, return cpu. */
function loadAndStep(cpu, code, steps) {
    cpu.load(new Uint8Array(code));
    for (let i = 0; i < steps; i++) {
        cpu.step();
        cpu.vuTick();
    }
    return cpu;
}

// ── VSET ─────────────────────────────────────────────────────────────

describe("VSET", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("VSET VL, imm16 sets vector length", () => {
        loadAndStep(cpu, [...vsetVL(100), Op.HLT], 1);
        expect(cpu.vu.regs.vl).toBe(100);
    });

    it("VSET VA, imm16 sets pointer", () => {
        loadAndStep(cpu, [...vsetPtr(0, 0x0200), Op.HLT], 1);
        expect(cpu.vu.regs.va).toBe(0x0200);
    });

    it("VSET VB, imm16 large address", () => {
        loadAndStep(cpu, [...vsetPtr(1, 25600), Op.HLT], 1);
        expect(cpu.vu.regs.vb).toBe(25600);
    });

    it("VSET GPR pair loads 16-bit from two GPRs", () => {
        // MOV A, 1; MOV D, 0x50; VSET VA, A, D → VA = (1 << 8) | 0x50 = 0x0150
        const code = [
            Op.MOV_REG_CONST,
            0,
            1, // MOV A, 1
            Op.MOV_REG_CONST,
            3,
            0x50, // MOV D, 0x50
            Op.VSET_GPR,
            0,
            (0 << 2) | 3, // VSET VA, A, D
            Op.HLT,
        ];
        loadAndStep(cpu, code, 3);
        expect(cpu.vu.regs.va).toBe(0x0150);
    });
});

// ── VFSTAT / VFCLR ───────────────────────────────────────────────────

describe("VFSTAT / VFCLR", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("VFSTAT reads VFPSR into GPR", () => {
        cpu.load(new Uint8Array([Op.VFSTAT, 0, Op.HLT]));
        cpu.vu.regs.vfpsr = 0x15;
        cpu.step();
        expect(cpu.a).toBe(0x15);
    });

    it("VFCLR clears VFPSR", () => {
        cpu.load(new Uint8Array([Op.VFCLR, Op.HLT]));
        cpu.vu.regs.vfpsr = 0xff;
        cpu.step();
        expect(cpu.vu.regs.vfpsr).toBe(0);
    });
});

// ── Async issue + queue ──────────────────────────────────────────────

describe("VU queue", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("async instruction enqueues command", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA
            ...vsetPtr(1, 260), // VB
            ...vsetPtr(2, 264), // VC
            ...vuAsync(Op.VADD, 5, 0, 2, 0, 1), // VADD.U VC, VA, VB
            Op.HLT,
        ];
        // Execute VSET instructions (4) + VADD (1) = 5 CPU steps, no VU ticks
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 5; i++) cpu.step();
        expect(cpu.vu.queueDepth).toBe(1);
        expect(cpu.vu.queueItems[0].label).toBe("VADD.U");
    });

    it("queue depth is 4", () => {
        const code = [...vsetVL(4), ...vsetPtr(0, 256), ...vsetPtr(1, 260), ...vsetPtr(2, 264)];
        // 4 VADD instructions
        for (let i = 0; i < 4; i++) {
            code.push(...vuAsync(Op.VADD, 5, 0, 2, 0, 1));
        }
        code.push(Op.HLT);
        cpu.load(new Uint8Array(code));
        // Execute 4 VSET + 4 VADD = 8 CPU steps, no VU ticks
        for (let i = 0; i < 8; i++) cpu.step();
        expect(cpu.vu.queueDepth).toBe(4);
        expect(cpu.vu.isFull).toBe(true);
    });

    it("vuTick processes one window from front command", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(2, 264),
            ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0), // VMOV.U VC, VA
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.step(); // VSET x3 + VMOV issue
        expect(cpu.vu.queueDepth).toBe(1);
        cpu.vuTick(); // process window
        expect(cpu.vu.queueDepth).toBe(0); // VL=4, window=8 → done in 1 tick
    });
});

// ── VMOV.U ───────────────────────────────────────────────────────────

describe("VMOV.U", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("copies bytes from src to dst", () => {
        // Set up source data at page 1 (addr 256)
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA = src
            ...vsetPtr(1, 260), // VB = dst
            ...vuAsync(Op.VMOV, 5, 0, 1, 0, 0), // VMOV.U VB, VA
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        // Write source data
        cpu.mem.set(256, 10);
        cpu.mem.set(257, 20);
        cpu.mem.set(258, 30);
        cpu.mem.set(259, 40);

        cpu.run(100);

        expect(cpu.mem.get(260)).toBe(10);
        expect(cpu.mem.get(261)).toBe(20);
        expect(cpu.mem.get(262)).toBe(30);
        expect(cpu.mem.get(263)).toBe(40);
    });
});

// ── VADD.U / VMUL.U ─────────────────────────────────────────────────

describe("VADD.U / VMUL.U", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("VADD.U adds two vectors element-wise", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA
            ...vsetPtr(1, 260), // VB
            ...vsetPtr(2, 264), // VC
            ...vuAsync(Op.VADD, 5, 0, 2, 0, 1), // VADD.U VC, VA, VB
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 10);
        cpu.mem.set(257, 20);
        cpu.mem.set(258, 30);
        cpu.mem.set(259, 40);
        cpu.mem.set(260, 1);
        cpu.mem.set(261, 2);
        cpu.mem.set(262, 3);
        cpu.mem.set(263, 4);

        cpu.run(100);

        expect(cpu.mem.get(264)).toBe(11);
        expect(cpu.mem.get(265)).toBe(22);
        expect(cpu.mem.get(266)).toBe(33);
        expect(cpu.mem.get(267)).toBe(44);
    });

    it("VADD.U wraps at 256", () => {
        const code = [
            ...vsetVL(1),
            ...vsetPtr(0, 256),
            ...vsetPtr(1, 257),
            ...vsetPtr(2, 258),
            ...vuAsync(Op.VADD, 5, 0, 2, 0, 1),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 200);
        cpu.mem.set(257, 100);

        cpu.run(100);

        expect(cpu.mem.get(258)).toBe(44); // (200+100) & 0xFF = 44
    });

    it("VMUL.U multiplies element-wise", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(1, 260),
            ...vsetPtr(2, 264),
            ...vuAsync(Op.VMUL, 5, 0, 2, 0, 1), // VMUL.U VC, VA, VB
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 2);
        cpu.mem.set(257, 3);
        cpu.mem.set(258, 1);
        cpu.mem.set(259, 4);
        cpu.mem.set(260, 10);
        cpu.mem.set(261, 20);
        cpu.mem.set(262, 30);
        cpu.mem.set(263, 40);

        cpu.run(100);

        expect(cpu.mem.get(264)).toBe(20);
        expect(cpu.mem.get(265)).toBe(60);
        expect(cpu.mem.get(266)).toBe(30);
        expect(cpu.mem.get(267)).toBe(160);
    });
});

// ── VADD.U reduction ─────────────────────────────────────────────────

describe("VADD.U reduction", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("reduces vector to scalar sum", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA = src
            ...vsetPtr(2, 260), // VC = dst
            ...vuAsync(Op.VADD, 5, 3, 2, 0, 0), // VADD.U.R VC, VA (mode=3 reduction)
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 10);
        cpu.mem.set(257, 20);
        cpu.mem.set(258, 30);
        cpu.mem.set(259, 40);

        cpu.run(100);

        expect(cpu.mem.get(260)).toBe(100); // 10+20+30+40
    });
});

// ── VWAIT ────────────────────────────────────────────────────────────

describe("VWAIT", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("stalls CPU until queue drains", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(2, 260),
            ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 5; i++) cpu.step(); // VSET x3 + VMOV + VWAIT
        expect(cpu.vuWaiting).toBe(true);
        expect(cpu.step()).toBe(false); // CPU stalled

        cpu.vuTick(); // drain (VL=4, window=8 → 1 tick)
        expect(cpu.vuWaiting).toBe(false);
        // Next step hits HLT → HALTED
        expect(cpu.step()).toBe(false);
        expect(cpu.state).toBe(CpuState.HALTED);
    });

    it("IP stays on VWAIT until queue empty", () => {
        const code = [
            ...vsetVL(64), // 64 elements, window=8 → 8 VU ticks
            ...vsetPtr(0, 256),
            ...vsetPtr(2, 512),
            ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        const vwaitAddr = 4 + 4 + 4 + 3; // offset of VWAIT
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 5; i++) cpu.step(); // issue all + VWAIT
        expect(cpu.ip).toBe(vwaitAddr); // IP on VWAIT

        cpu.vuTick(); // tick 1/8
        expect(cpu.ip).toBe(vwaitAddr); // still on VWAIT

        for (let i = 0; i < 7; i++) cpu.vuTick(); // ticks 2-8
        expect(cpu.ip).toBe(vwaitAddr + 1); // IP advanced past VWAIT
    });
});

// ── VL=0 ─────────────────────────────────────────────────────────────

describe("VL=0", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("async instruction is no-op when VL=0", () => {
        const code = [...vsetVL(0), ...vsetPtr(0, 256), ...vsetPtr(2, 260), ...vuAsync(Op.VADD, 5, 0, 2, 0, 0), Op.HLT];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(260, 99);
        cpu.run(50);
        expect(cpu.mem.get(260)).toBe(99); // unchanged
        expect(cpu.vu.queueDepth).toBe(0);
    });
});

// ── Auto-increment ───────────────────────────────────────────────────

describe("Auto-increment", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("pointers advance by VL*elemSize after async issue", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA
            ...vsetPtr(1, 260), // VB
            ...vsetPtr(2, 264), // VC
            ...vuAsync(Op.VADD, 5, 0, 2, 0, 1), // VADD.U VC, VA, VB
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 5; i++) cpu.step();
        // U format, elemSize=1, VL=4 → each pointer advances by 4
        expect(cpu.vu.regs.va).toBe(260);
        expect(cpu.vu.regs.vb).toBe(264);
        expect(cpu.vu.regs.vc).toBe(268);
    });
});

// ── Window execution model ───────────────────────────────────────────

describe("Window execution", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("VL=32 U-format takes 4 VU ticks (window=8)", () => {
        const code = [
            ...vsetVL(32),
            ...vsetPtr(0, 256),
            ...vsetPtr(2, 512),
            ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0),
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.step();
        expect(cpu.vu.queueDepth).toBe(1);

        cpu.vuTick(); // tick 1: elements 0-7
        expect(cpu.vu.queueDepth).toBe(1); // not done yet

        cpu.vuTick(); // tick 2: elements 8-15
        expect(cpu.vu.queueDepth).toBe(1); // not done yet

        cpu.vuTick(); // tick 3: elements 16-23
        expect(cpu.vu.queueDepth).toBe(1); // not done yet

        cpu.vuTick(); // tick 4: elements 24-31
        expect(cpu.vu.queueDepth).toBe(0); // done
    });

    it("VL=4 U-format completes in 1 VU tick", () => {
        const code = [...vsetVL(4), ...vsetPtr(0, 256), ...vsetPtr(2, 260), ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0), Op.HLT];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.step();
        expect(cpu.vu.queueDepth).toBe(1);

        cpu.vuTick();
        expect(cpu.vu.queueDepth).toBe(0);
    });

    it("back-to-back issue accumulates queue depth 2 (window=8)", () => {
        // Two VMOV.U with VL=16 back-to-back using auto-increment.
        // Each needs ceil(16/8)=2 VU ticks.
        // At issue of #2, #1 has only had 1 VU tick (half done) → depth=2.
        const code = [
            ...vsetVL(16),
            ...vsetPtr(0, 256), // VA = src
            ...vsetPtr(2, 512), // VB = dst
            ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0), // issue #1 (auto-inc VA,VB)
            ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0), // issue #2
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));

        // Execute 3 VSETs + issue #1
        for (let i = 0; i < 4; i++) cpu.step();
        expect(cpu.vu.queueDepth).toBe(1); // VMOV#1 queued

        cpu.vuTick(); // VU processes VMOV#1 window 0..7 (still half done)
        cpu.step(); // CPU issues VMOV#2
        expect(cpu.vu.queueDepth).toBe(2); // both in queue
    });
});

// ── VFM validation ───────────────────────────────────────────────────

describe("VFM validation", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("reserved format (7) causes FAULT", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(2, 260),
            ...vuAsync(Op.VADD, 7, 0, 2, 0, 0), // fmt=7 reserved
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.step();
        expect(cpu.state).toBe(CpuState.FAULT);
    });
});
