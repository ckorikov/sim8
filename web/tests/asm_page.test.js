/**
 * Tests for @page directive and {label} expression in the assembler.
 */

import { describe, it, expect } from "vitest";
import { assemble, AsmError } from "../lib/asm.js";

// ── Helpers ─────────────────────────────────────────────────────────

function asm(source, arch = 2) {
    return assemble(source, arch).code;
}

function labels(source, arch = 2) {
    return assemble(source, arch).labels;
}

function asmError(source, arch = 2) {
    let caught;
    try {
        assemble(source, arch);
    } catch (e) {
        caught = e;
    }
    expect(caught).toBeInstanceOf(AsmError);
    return caught;
}

// ── @page directive parsing ──────────────────────────────────────────

describe("@page directive parsing", () => {
    it("@page 0 → valid", () => {
        const c = asm("@page 0\nHLT\n@page 1\nDB 42");
        expect(c[0]).toBe(0); // HLT
        expect(c[256]).toBe(42);
    });

    it("@page 0, M → offset", () => {
        const c = asm("HLT\n@page 0, 10\nDB 42\n@page 1\nDB 1");
        expect(c[0]).toBe(0); // HLT
        expect(c[10]).toBe(42);
    });

    it("@page 1, M → offset on page 1", () => {
        const c = asm("HLT\n@page 1, 10\nDB 42");
        expect(c[256 + 10]).toBe(42);
    });

    it("@page 256 → error", () => {
        expect(asmError("@page 256").message).toContain("must be 0-255");
    });

    it("@page offset invalid → error", () => {
        expect(asmError("@page 1, abc").message).toContain("invalid offset");
    });

    it("@page offset out of range → error", () => {
        expect(asmError("@page 1, 256").message).toContain("offset must be 0-255");
    });

    it("@page without number → error", () => {
        expect(asmError("@page").message).toContain("missing page number");
    });

    it("@page with non-number → error", () => {
        expect(asmError("@page abc").message).toContain("invalid syntax");
    });

    it("@page hex value", () => {
        const c = asm("HLT\n@page 0xFF\nDB 42");
        expect(c.length).toBe(256 * 256); // page 0-255
        expect(c[255 * 256]).toBe(42);
    });

    it("@page with comment", () => {
        const c = asm("HLT\n@page 1 ; data\nDB 42");
        expect(c[256]).toBe(42);
    });

    it("@page case insensitive", () => {
        const c = asm("HLT\n@PAGE 1\nDB 42");
        expect(c[256]).toBe(42);
    });

    it("label on @page line → error", () => {
        expect(asmError("label: @page 1").message).toMatch(/syntax error|invalid/i);
    });
});

// ── {label} expression ──────────────────────────────────────────────

describe("{label} expression", () => {
    it("{label} resolves to page number", () => {
        const c = asm("MOV DP, {data}\nHLT\n@page 1\ndata: DB 42");
        expect(c[2]).toBe(1); // page number
    });

    it("{label} for page 0 → 0", () => {
        const c = asm("start: HLT\nMOV A, {start}");
        expect(c[3]).toBe(0);
    });

    it("{} is an error", () => {
        expect(asmError("MOV A, {}").message).toMatch(/invalid operand/i);
    });

    it("{123} is an error", () => {
        expect(asmError("MOV A, {123}").message).toMatch(/syntax error/i);
    });

    it("[{x}] is an error", () => {
        expect(asmError("MOV A, [{x}]").message).toMatch(/invalid address/i);
    });

    it("{undefined} is an error", () => {
        expect(asmError("MOV DP, {undefined}\nHLT").message).toMatch(/undefined label/i);
    });

    it("{label} works with PUSH", () => {
        const c = asm("PUSH {data}\nHLT\n@page 2\ndata: DB 1");
        expect(c[1]).toBe(2);
    });

    it("{label} works with CMP", () => {
        const c = asm("CMP A, {data}\nHLT\n@page 3\ndata: DB 1");
        expect(c[2]).toBe(3);
    });
});

// ── Basic @page assembly ────────────────────────────────────────────

describe("@page assembly", () => {
    it("data on page 1", () => {
        const c = asm("HLT\n@page 1\nDB 65, 66, 67");
        expect(c.length).toBe(512);
        expect(c[256]).toBe(65);
        expect(c[257]).toBe(66);
        expect(c[258]).toBe(67);
    });

    it("multiple pages", () => {
        const c = asm("HLT\n@page 1\nDB 10\n@page 2\nDB 20");
        expect(c.length).toBe(768);
        expect(c[256]).toBe(10);
        expect(c[512]).toBe(20);
    });

    it("non-sequential pages", () => {
        const c = asm("HLT\n@page 3\nDB 30\n@page 1\nDB 10");
        expect(c.length).toBe(1024);
        expect(c[768]).toBe(30);
        expect(c[256]).toBe(10);
    });

    it("no @page → backward compat (no padding)", () => {
        const c = asm("MOV A, 42\nHLT");
        expect(c.length).toBe(4);
    });

    it("page 0 padded to 256 with @page", () => {
        const c = asm("HLT\n@page 1\nDB 1");
        expect(c.length).toBe(512);
        expect(c[0]).toBe(0); // HLT
        expect(c[255]).toBe(0); // padding
        expect(c[256]).toBe(1); // page 1
    });

    it("sparse pages are zero-filled", () => {
        const c = asm("HLT\n@page 3\nDB 42");
        expect(c.length).toBe(1024);
        for (let i = 256; i < 768; i++) {
            expect(c[i]).toBe(0);
        }
        expect(c[768]).toBe(42);
    });
});

// ── Labels with @page ───────────────────────────────────────────────

describe("labels with @page", () => {
    it("label on page 1 has memory address", () => {
        const l = labels("HLT\n@page 1\nmatrix: DB 42");
        expect(l.matrix).toBe(256);
    });

    it("label offset within page", () => {
        const l = labels("HLT\n@page 1\nDB 0, 0, 0\ntarget: DB 42");
        expect(l.target).toBe(259);
    });

    it("regular label gives page-local offset", () => {
        const c = asm("MOV A, [data]\nHLT\n@page 1\ndata: DB 42");
        expect(c[1]).toBe(0); // offset 0 within page
    });
});

// ── Cross-page jump validation ──────────────────────────────────────

describe("cross-page jumps", () => {
    it("JMP page 0 → page 1 → error", () => {
        expect(asmError("JMP target\n@page 1\ntarget: DB 42").message).toMatch(/jump target/i);
    });

    it("CALL page 0 → page 1 → error", () => {
        expect(asmError("CALL target\n@page 1\ntarget: DB 42").message).toMatch(/jump target/i);
    });

    it("conditional jump cross-page → error", () => {
        expect(asmError("JE target\n@page 1\ntarget: DB 42").message).toContain("page 1");
    });

    it("JMP same page > 0 → OK", () => {
        const c = asm("HLT\n@page 1\nstart: MOV A, 1\nJMP start");
        expect(c.length).toBe(512);
    });

    it("cross-page page 2 → page 1 → error", () => {
        expect(asmError("HLT\n@page 1\ntarget: DB 42\n@page 2\nJMP target").message).toMatch(/cross-page/i);
    });

    it("MOV with cross-page label is OK (not a jump)", () => {
        const c = asm("MOV A, [data]\nHLT\n@page 1\ndata: DB 42");
        expect(c.length).toBe(512);
    });
});

// ── @page errors ────────────────────────────────────────────────────

describe("@page errors", () => {
    it("page overflow", () => {
        const data = new Array(257).fill("0").join(", ");
        expect(asmError(`HLT\n@page 1\nDB ${data}`).message).toMatch(/overflow/i);
    });

    it("offset before current position → error", () => {
        expect(asmError("HLT\nMOV A, 1\n@page 0, 1").message).toContain("before current position");
    });
});

// ── @page offset ───────────────────────────────────────────────────

describe("@page offset", () => {
    it("@page 0 resume after @page 1", () => {
        const c = asm("MOV A, 1\n@page 1\nDB 42\n@page 0\nHLT");
        expect(c[0]).toBe(6); // MOV opcode
        expect(c[3]).toBe(0); // HLT (resumed)
        expect(c[256]).toBe(42);
    });

    it("@page N (N>0) resume after switch", () => {
        const c = asm("HLT\n@page 1\nDB 1\n@page 2\nDB 2\n@page 1\nDB 3");
        expect(c[256]).toBe(1);
        expect(c[257]).toBe(3); // resumed
    });

    it("@page 0, M resume with offset", () => {
        const c = asm("DB 1, 2\n@page 1\nDB 42\n@page 0, 10\nDB 99");
        expect(c[0]).toBe(1);
        expect(c[1]).toBe(2);
        expect(c[10]).toBe(99);
        expect(c[256]).toBe(42);
    });

    it("label after @page 0, M gets correct offset", () => {
        const c = asm("JMP loader\n@page 0, 20\nloader: HLT\n@page 1\nDB 1");
        expect(c[1]).toBe(20); // JMP target
        expect(c[20]).toBe(0); // HLT
    });

    it("zero-filled gap", () => {
        const c = asm("HLT\n@page 1, 5\nDB 42");
        for (let i = 256; i < 261; i++) {
            expect(c[i]).toBe(0);
        }
        expect(c[261]).toBe(42);
    });
});

// ── Overlay code ────────────────────────────────────────────────────

describe("overlay code", () => {
    it("instructions on page > 0", () => {
        const c = asm("HLT\n@page 1\nMOV A, 42\nHLT");
        expect(c[256]).toBe(6); // MOV opcode
        expect(c[257]).toBe(0); // reg A
        expect(c[258]).toBe(42);
        expect(c[259]).toBe(0); // HLT
    });

    it("labels in overlay use page-local offsets", () => {
        const r = assemble("HLT\n@page 2\nstart: MOV A, 1\nloop: JMP loop");
        expect(r.labels.start).toBe(512);
        expect(r.labels.loop).toBe(515);
        // JMP loop target = page-local offset 3
        expect(r.code[515 + 1]).toBe(3);
    });

    it("{label} in overlay resolves to page number", () => {
        const c = asm("HLT\n@page 1\ndata: DB 42\n@page 2\nMOV DP, {data}");
        expect(c[514]).toBe(1);
    });
});
