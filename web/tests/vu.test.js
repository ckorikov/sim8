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

    it("VSET single GPR zero-extends 8-bit value", () => {
        // MOV A, 42; VSET VL, A → VL = 42
        const code = [
            Op.MOV_REG_CONST,
            0,
            42, // MOV A, 42
            Op.VSET_GPR,
            4,
            0x10, // VSET VL, A (bit 4 set, gpr=0)
            Op.HLT,
        ];
        loadAndStep(cpu, code, 2);
        expect(cpu.vu.regs.vl).toBe(42);
    });

    it("VSET single GPR with register B", () => {
        // MOV B, 200; VSET VL, B → VL = 200
        const code = [
            Op.MOV_REG_CONST,
            1,
            200, // MOV B, 200
            Op.VSET_GPR,
            4,
            0x11, // VSET VL, B (bit 4 set, gpr=1)
            Op.HLT,
        ];
        loadAndStep(cpu, code, 2);
        expect(cpu.vu.regs.vl).toBe(200);
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

// ── VGATHER / VSCATTER ──────────────────────────────────────────────

describe("VGATHER", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("compress: picks every 4th byte (stride-4 mask)", () => {
        // Source: 8 BGRA bytes at 256, Mask at 280, Dest at 300
        const code = [
            ...vsetVL(8),
            ...vsetPtr(0, 256), // VA = source
            ...vsetPtr(1, 300), // VB = dest
            ...vsetPtr(3, 280), // VM = mask
            ...vuAsync(Op.VGATHER, 5, 0, 1, 0, 0), // VGATHER.U VB, VA
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        // BGRA pixels
        cpu.mem.set(256, 10);
        cpu.mem.set(257, 20);
        cpu.mem.set(258, 30);
        cpu.mem.set(259, 40);
        cpu.mem.set(260, 50);
        cpu.mem.set(261, 60);
        cpu.mem.set(262, 70);
        cpu.mem.set(263, 80);
        // Mask: select every 4th
        cpu.mem.set(280, 0xff);
        cpu.mem.set(281, 0);
        cpu.mem.set(282, 0);
        cpu.mem.set(283, 0);
        cpu.mem.set(284, 0xff);
        cpu.mem.set(285, 0);
        cpu.mem.set(286, 0);
        cpu.mem.set(287, 0);

        cpu.run(100);

        expect(cpu.state).toBe(CpuState.HALTED);
        expect(cpu.mem.get(300)).toBe(10);
        expect(cpu.mem.get(301)).toBe(50);
        expect(cpu.mem.get(302)).toBe(0); // untouched
    });

    it("compress: all-ones mask copies everything", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(1, 300),
            ...vsetPtr(3, 280),
            ...vuAsync(Op.VGATHER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.mem.set(256 + i, 10 + i);
        for (let i = 0; i < 4; i++) cpu.mem.set(280 + i, 0xff);

        cpu.run(100);

        expect(cpu.state).toBe(CpuState.HALTED);
        for (let i = 0; i < 4; i++) expect(cpu.mem.get(300 + i)).toBe(10 + i);
    });

    it("compress: all-zeros mask writes nothing", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(1, 300),
            ...vsetPtr(3, 280),
            ...vuAsync(Op.VGATHER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.mem.set(256 + i, 99);
        // mask all zeros (default)

        cpu.run(100);

        expect(cpu.state).toBe(CpuState.HALTED);
        expect(cpu.mem.get(300)).toBe(0); // untouched
    });

    it("auto-increment: VA += VL, VB and VM unchanged", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(1, 300),
            ...vsetPtr(3, 280),
            ...vuAsync(Op.VGATHER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.mem.set(280 + i, 0xff);

        cpu.run(100);

        expect(cpu.vu.regs.va).toBe(260); // VA += 4
        expect(cpu.vu.regs.vb).toBe(300); // VB unchanged (data-dependent)
        expect(cpu.vu.regs.vm).toBe(280); // VM unchanged (reusable pattern)
    });

    it("VL=0 is no-op", () => {
        const code = [
            ...vsetVL(0),
            ...vsetPtr(0, 256),
            ...vsetPtr(1, 300),
            ...vuAsync(Op.VGATHER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.run(100);
        expect(cpu.state).toBe(CpuState.HALTED);
    });

    it("multi-window: VL=16 spans 2 windows, compactIdx persists", () => {
        // 16 bytes source, mask selects every other byte (8 selected)
        const code = [
            ...vsetVL(16),
            ...vsetPtr(0, 256), // VA = source
            ...vsetPtr(1, 300), // VB = dest
            ...vsetPtr(3, 400), // VM = mask
            ...vuAsync(Op.VGATHER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 16; i++) cpu.mem.set(256 + i, 10 + i);
        // Mask: every other byte
        for (let i = 0; i < 16; i++) cpu.mem.set(400 + i, i % 2 === 0 ? 0xff : 0);

        cpu.run(200);

        expect(cpu.state).toBe(CpuState.HALTED);
        // Selected: indices 0,2,4,6,8,10,12,14 → values 10,12,14,16,18,20,22,24
        for (let i = 0; i < 8; i++) {
            expect(cpu.mem.get(300 + i)).toBe(10 + i * 2);
        }
    });
});

describe("VSCATTER", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("expand: spreads packed bytes into stride-4 positions", () => {
        // Packed source: [10, 50] at 256, Mask at 280, Dest at 300
        const code = [
            ...vsetVL(8),
            ...vsetPtr(0, 256), // VA = packed source
            ...vsetPtr(1, 300), // VB = dest
            ...vsetPtr(3, 280), // VM = mask
            ...vuAsync(Op.VSCATTER, 5, 0, 1, 0, 0), // VSCATTER.U VB, VA
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 10);
        cpu.mem.set(257, 50);
        // Mask: positions 0 and 4
        cpu.mem.set(280, 0xff);
        cpu.mem.set(281, 0);
        cpu.mem.set(282, 0);
        cpu.mem.set(283, 0);
        cpu.mem.set(284, 0xff);
        cpu.mem.set(285, 0);
        cpu.mem.set(286, 0);
        cpu.mem.set(287, 0);

        cpu.run(100);

        expect(cpu.state).toBe(CpuState.HALTED);
        expect(cpu.mem.get(300)).toBe(10);
        expect(cpu.mem.get(301)).toBe(0);
        expect(cpu.mem.get(302)).toBe(0);
        expect(cpu.mem.get(303)).toBe(0);
        expect(cpu.mem.get(304)).toBe(50);
    });

    it("round-trip: gather then scatter restores original", () => {
        // Source BGRA: [10,20,30,40, 50,60,70,80] at 256
        // Gather to 300, then scatter back to 400
        const code = [
            ...vsetVL(8),
            ...vsetPtr(0, 256), // VA = BGRA source
            ...vsetPtr(1, 300), // VB = gather dest
            ...vsetPtr(3, 280), // VM = mask
            ...vuAsync(Op.VGATHER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            // Now scatter: packed at 300 → expanded at 400
            ...vsetPtr(0, 300), // VA = packed
            ...vsetPtr(1, 400), // VB = dest
            ...vsetPtr(3, 280), // VM = same mask
            ...vuAsync(Op.VSCATTER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 10);
        cpu.mem.set(257, 20);
        cpu.mem.set(258, 30);
        cpu.mem.set(259, 40);
        cpu.mem.set(260, 50);
        cpu.mem.set(261, 60);
        cpu.mem.set(262, 70);
        cpu.mem.set(263, 80);
        cpu.mem.set(280, 0xff);
        cpu.mem.set(281, 0);
        cpu.mem.set(282, 0);
        cpu.mem.set(283, 0);
        cpu.mem.set(284, 0xff);
        cpu.mem.set(285, 0);
        cpu.mem.set(286, 0);
        cpu.mem.set(287, 0);

        cpu.run(200);

        expect(cpu.state).toBe(CpuState.HALTED);
        // Gathered: [10, 50]
        expect(cpu.mem.get(300)).toBe(10);
        expect(cpu.mem.get(301)).toBe(50);
        // Scattered back: positions 0,4 get 10,50
        expect(cpu.mem.get(400)).toBe(10);
        expect(cpu.mem.get(401)).toBe(0);
        expect(cpu.mem.get(404)).toBe(50);
    });

    it("auto-increment: VB += VL, VA and VM unchanged", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(1, 300),
            ...vsetPtr(3, 280),
            ...vuAsync(Op.VSCATTER, 5, 0, 1, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.mem.set(280 + i, 0xff);

        cpu.run(100);

        expect(cpu.vu.regs.va).toBe(256); // VA unchanged (data-dependent src)
        expect(cpu.vu.regs.vb).toBe(304); // VB += 4
        expect(cpu.vu.regs.vm).toBe(280); // VM unchanged
    });
});

// ── VEXP / VFMADD / VMOV broadcast — new in arch 3 ─────────────────

const FP_FMT_F = 0;
const FP_FMT_BF = 2;
const FP_FMT_O3 = 3;

function readF32(mem, addr) {
    const buf = new ArrayBuffer(4);
    const u8 = new Uint8Array(buf);
    for (let i = 0; i < 4; i++) u8[i] = mem.get(addr + i);
    return new Float32Array(buf)[0];
}

function readBf16(mem, addr) {
    const lo = mem.get(addr);
    const hi = mem.get(addr + 1);
    const buf = new ArrayBuffer(4);
    const u8 = new Uint8Array(buf);
    u8[0] = 0;
    u8[1] = 0;
    u8[2] = lo;
    u8[3] = hi;
    return new Float32Array(buf)[0];
}

describe("VEXP", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("element-wise exp on bf16", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA = 256
            ...vsetPtr(2, 256), // VC = 256 (in-place)
            ...vuAsync(Op.VEXP, FP_FMT_BF, 0, 2, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        // Write 0.0, 1.0, 2.0, -1.0 as bf16
        const vals = [0.0, 1.0, 2.0, -1.0];
        for (let i = 0; i < vals.length; i++) {
            const buf = new ArrayBuffer(4);
            new Float32Array(buf)[0] = vals[i];
            const u8 = new Uint8Array(buf);
            cpu.mem.set(256 + i * 2, u8[2]);
            cpu.mem.set(256 + i * 2 + 1, u8[3]);
        }
        cpu.run(100);
        const expected = [1.0, Math.E, Math.exp(2), Math.exp(-1)];
        for (let i = 0; i < 4; i++) {
            const got = readBf16(cpu.mem, 256 + i * 2);
            expect(Math.abs(got - expected[i]) / Math.max(expected[i], 1e-9)).toBeLessThan(0.05);
        }
    });

    it("integer format → FAULT(VU_FORMAT)", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(2, 256),
            ...vuAsync(Op.VEXP, 5, 0, 2, 0, 0), // fmt=U
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.run(100);
        expect(cpu.state).toBe(CpuState.FAULT);
    });
});

describe("VFMADD", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("fused multiply-add f32 vv mode", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA
            ...vsetPtr(1, 272), // VB
            ...vsetPtr(2, 288), // VC (accumulator)
            ...vuAsync(Op.VFMADD, FP_FMT_F, 0, 2, 0, 1),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));

        const writeF32 = (addr, val) => {
            const buf = new ArrayBuffer(4);
            new Float32Array(buf)[0] = val;
            const u8 = new Uint8Array(buf);
            for (let i = 0; i < 4; i++) cpu.mem.set(addr + i, u8[i]);
        };
        const va = [1.0, 2.0, 3.0, 4.0];
        const vb = [5.0, 6.0, 7.0, 8.0];
        const vc = [0.5, 1.0, 1.5, 2.0];
        for (let i = 0; i < 4; i++) {
            writeF32(256 + i * 4, va[i]);
            writeF32(272 + i * 4, vb[i]);
            writeF32(288 + i * 4, vc[i]);
        }

        cpu.run(200);

        for (let i = 0; i < 4; i++) {
            const got = readF32(cpu.mem, 288 + i * 4);
            expect(got).toBeCloseTo(vc[i] + va[i] * vb[i], 5);
        }
    });

    it("integer format → FAULT", () => {
        const code = [...vsetVL(4), ...vuAsync(Op.VFMADD, 5, 0, 2, 0, 1), Op.HLT];
        cpu.load(new Uint8Array(code));
        cpu.run(100);
        expect(cpu.state).toBe(CpuState.FAULT);
    });

    it("reduction mode → FAULT (no r-mode for VFMADD)", () => {
        const code = [...vsetVL(4), ...vuAsync(Op.VFMADD, FP_FMT_F, 3 /* r */, 2, 0, 0), Op.HLT];
        cpu.load(new Uint8Array(code));
        cpu.run(100);
        expect(cpu.state).toBe(CpuState.FAULT);
    });
});

describe("VMOV broadcast (vs/vi)", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("VMOV.U vi broadcasts immediate", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(2, 256), // VC
            Op.VMOV,
            encodeVfm(5, 2, 0), // fmt=U, mode=vi
            encodeVuRegs(2, 0, 0),
            0x55,
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.mem.set(256 + i, 0xaa);
        cpu.run(100);
        for (let i = 0; i < 4; i++) expect(cpu.mem.get(256 + i)).toBe(0x55);
    });

    it("VMOV.BF vs reads bf16 scalar from mem[VB], broadcasts to VC", () => {
        // mem[256..257] = bf16(1.5) = LE 0xC0 0x3F. VC at 264..271.
        const code = [
            ...vsetVL(4),
            ...vsetPtr(1, 256), // VB = scalar address
            ...vsetPtr(2, 264), // VC = output buffer
            // VMOV.BF mode=vs (1) — s2 = VB (code 1)
            Op.VMOV,
            encodeVfm(2, 1, 0), // fmt=BF=2, mode=vs=1
            encodeVuRegs(2, 0, 1), // dst=VC, src1=VA(unused), s2=VB
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 0xc0);
        cpu.mem.set(257, 0x3f);
        cpu.run(100);
        for (let i = 0; i < 4; i++) {
            expect(cpu.mem.get(264 + i * 2)).toBe(0xc0);
            expect(cpu.mem.get(264 + i * 2 + 1)).toBe(0x3f);
        }
        // VB does NOT advance in vs mode (snapshot once); VC advances by VL*sz
        expect(cpu.vu.regs.vb).toBe(256);
        expect(cpu.vu.regs.vc).toBe(272);
    });

    it("VMOV.U vs broadcasts byte from mem[VB]", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(1, 256), // VB → scalar
            ...vsetPtr(2, 260), // VC → output
            Op.VMOV,
            encodeVfm(5, 1, 0), // fmt=U=5, mode=vs=1
            encodeVuRegs(2, 0, 1), // dst=VC, src1=VA(unused), s2=VB
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        cpu.mem.set(256, 0x77);
        cpu.run(100);
        for (let i = 0; i < 4; i++) expect(cpu.mem.get(260 + i)).toBe(0x77);
    });

    it("VMOV.U vv still does raw byte copy", () => {
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256),
            ...vsetPtr(2, 260),
            ...vuAsync(Op.VMOV, 5, 0, 2, 0, 0),
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        for (let i = 0; i < 4; i++) cpu.mem.set(256 + i, 0x10 + i);
        cpu.run(100);
        for (let i = 0; i < 4; i++) expect(cpu.mem.get(260 + i)).toBe(0x10 + i);
    });
});

describe("VADD vi imm decoding (regression)", () => {
    let cpu;
    beforeEach(() => {
        cpu = makeCPU();
    });

    it("VADD.O3 with vi imm = O3-encoded byte for 1.0 (0x38)", () => {
        // Previously cmd.imm was used as a raw float (0x38 → 56.0); now decoded
        // as 1.0 in O3 format.
        const code = [
            ...vsetVL(4),
            ...vsetPtr(0, 256), // VA
            ...vsetPtr(2, 260), // VC
            Op.VADD,
            encodeVfm(FP_FMT_O3, 2, 0), // mode=vi
            encodeVuRegs(2, 0, 0),
            0x38, // 1.0 in O3
            Op.VWAIT,
            Op.HLT,
        ];
        cpu.load(new Uint8Array(code));
        // VA[i] = 1.0_o3 (0x38) for all 4 elements
        for (let i = 0; i < 4; i++) cpu.mem.set(256 + i, 0x38);
        cpu.run(100);
        // Result: 1.0 + 1.0 = 2.0 in O3 = 0x40
        for (let i = 0; i < 4; i++) expect(cpu.mem.get(260 + i)).toBe(0x40);
    });
});
