/**
 * Tests for breakpoints.js — global BP registry.
 */

import { describe, it, expect, beforeEach } from "vitest";
import { breakpoints } from "../src/breakpoints.js";

beforeEach(() => breakpoints.clearAll());

// ── toggle / has ─────────────────────────────────────────────────

describe("toggle + has", () => {
    it("adds a breakpoint", () => {
        breakpoints.toggle("main.asm", 5);
        expect(breakpoints.has("main.asm", 5)).toBe(true);
    });

    it("removes on second toggle", () => {
        breakpoints.toggle("main.asm", 5);
        breakpoints.toggle("main.asm", 5);
        expect(breakpoints.has("main.asm", 5)).toBe(false);
    });

    it("different lines are independent", () => {
        breakpoints.toggle("main.asm", 3);
        breakpoints.toggle("main.asm", 7);
        expect(breakpoints.has("main.asm", 3)).toBe(true);
        expect(breakpoints.has("main.asm", 7)).toBe(true);
        breakpoints.toggle("main.asm", 3);
        expect(breakpoints.has("main.asm", 3)).toBe(false);
        expect(breakpoints.has("main.asm", 7)).toBe(true);
    });

    it("different files are independent", () => {
        breakpoints.toggle("main.asm", 1);
        breakpoints.toggle("lib.asm", 1);
        expect(breakpoints.has("main.asm", 1)).toBe(true);
        expect(breakpoints.has("lib.asm", 1)).toBe(true);
        breakpoints.toggle("main.asm", 1);
        expect(breakpoints.has("main.asm", 1)).toBe(false);
        expect(breakpoints.has("lib.asm", 1)).toBe(true);
    });

    it("returns false for line that was never set", () => {
        expect(breakpoints.has("main.asm", 99)).toBe(false);
    });

    it("null file maps to main.asm", () => {
        breakpoints.toggle(null, 10);
        expect(breakpoints.has("main.asm", 10)).toBe(true);
        expect(breakpoints.has(null, 10)).toBe(true);
    });
});

// ── getForFile ───────────────────────────────────────────────────

describe("getForFile", () => {
    it("returns empty set for unknown file", () => {
        expect(breakpoints.getForFile("nope.asm").size).toBe(0);
    });

    it("returns all lines for the file", () => {
        breakpoints.toggle("a.asm", 2);
        breakpoints.toggle("a.asm", 5);
        const set = breakpoints.getForFile("a.asm");
        expect(set).toEqual(new Set([2, 5]));
    });

    it("null file returns main.asm BPs", () => {
        breakpoints.toggle("main.asm", 3);
        expect(breakpoints.getForFile(null).has(3)).toBe(true);
    });
});

// ── renameFile ───────────────────────────────────────────────────

describe("renameFile", () => {
    it("migrates BPs to new name", () => {
        breakpoints.toggle("old.asm", 4);
        breakpoints.toggle("old.asm", 8);
        breakpoints.renameFile("old.asm", "new.asm");
        expect(breakpoints.getForFile("old.asm").size).toBe(0);
        expect(breakpoints.getForFile("new.asm")).toEqual(new Set([4, 8]));
    });

    it("no-op when file has no BPs", () => {
        breakpoints.renameFile("ghost.asm", "renamed.asm");
        expect(breakpoints.getForFile("renamed.asm").size).toBe(0);
    });
});

// ── clearFile / clearAll ─────────────────────────────────────────

describe("clearFile", () => {
    it("removes only the specified file", () => {
        breakpoints.toggle("a.asm", 1);
        breakpoints.toggle("b.asm", 2);
        breakpoints.clearFile("a.asm");
        expect(breakpoints.has("a.asm", 1)).toBe(false);
        expect(breakpoints.has("b.asm", 2)).toBe(true);
    });
});

describe("clearAll", () => {
    it("removes BPs across all files", () => {
        breakpoints.toggle("main.asm", 1);
        breakpoints.toggle("lib.asm", 5);
        breakpoints.clearAll();
        expect(breakpoints.has("main.asm", 1)).toBe(false);
        expect(breakpoints.has("lib.asm", 5)).toBe(false);
    });
});

// ── checkFlat ────────────────────────────────────────────────────

describe("checkFlat", () => {
    it("returns false for undefined flatLine", () => {
        expect(breakpoints.checkFlat(undefined, null)).toBe(false);
    });

    it("single-file mode (no lineMap): flatLine === original line", () => {
        breakpoints.toggle("main.asm", 7);
        expect(breakpoints.checkFlat(7, null)).toBe(true);
        expect(breakpoints.checkFlat(8, null)).toBe(false);
    });

    it("multi-file: resolves via lineMap to correct file+line", () => {
        const lineMap = new Map([
            [1, { file: null, line: 1 }], // main.asm line 1
            [2, { file: "lib.asm", line: 10 }], // lib.asm line 10
            [3, { file: "lib.asm", line: 11 }],
        ]);
        breakpoints.toggle("main.asm", 1);
        breakpoints.toggle("lib.asm", 10);

        expect(breakpoints.checkFlat(1, lineMap)).toBe(true); // main, line 1 ✓
        expect(breakpoints.checkFlat(2, lineMap)).toBe(true); // lib, line 10 ✓
        expect(breakpoints.checkFlat(3, lineMap)).toBe(false); // lib, line 11 no BP
    });

    it("multi-file: flat line without BP returns false", () => {
        const lineMap = new Map([[5, { file: "a.asm", line: 3 }]]);
        expect(breakpoints.checkFlat(5, lineMap)).toBe(false);
    });

    it("empty lineMap: falls back to flatLine as original line", () => {
        const lineMap = new Map();
        breakpoints.toggle("main.asm", 4);
        expect(breakpoints.checkFlat(4, lineMap)).toBe(true);
    });
});
