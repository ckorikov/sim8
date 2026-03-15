/**
 * Tests for tab management + breakpoints integration.
 * tabs.js has DOM dependencies → mock editor.js and drive via the exported API.
 */

import { describe, it, expect, beforeEach, vi } from "vitest";

// ── Mock editor.js (DOM-dependent) ───────────────────────────────

let _editorSource = "";
let _onBpToggle = null;
let _cmBps = new Set();

vi.mock("../src/editor.js", () => ({
    getEditorSource: () => _editorSource,
    setEditorSource: (text) => {
        _editorSource = text;
    },
    clearExecLine: vi.fn(),
    focusEditor: vi.fn(),
    setOnBpToggle: (fn) => {
        _onBpToggle = fn;
    },
    syncBpFromStore: (set) => {
        _cmBps = new Set(set);
    },
}));

// Mock DOM (tab-bar not needed for logic tests — renderTabBar guards on getElementById)
vi.stubGlobal("document", {
    getElementById: () => null,
    addEventListener: vi.fn(),
    elementFromPoint: () => null,
    createElement: () => ({
        className: "",
        dataset: {},
        textContent: "",
        title: "",
        addEventListener: vi.fn(),
        appendChild: vi.fn(),
        querySelector: vi.fn(),
        contains: () => false,
    }),
});

// ── Import after mocks ────────────────────────────────────────────

import { breakpoints } from "../src/breakpoints.js";
import { initTabs, saveCurrentTab, getMainSource, getVirtualFiles, switchTabForExec } from "../src/tabs.js";

// ── Helpers ──────────────────────────────────────────────────────

function init() {
    breakpoints.clearAll();
    _editorSource = "";
    _cmBps = new Set();
    initTabs();
}

beforeEach(init);

// ── initTabs ─────────────────────────────────────────────────────

describe("initTabs", () => {
    it("registers a BP toggle callback", () => {
        expect(_onBpToggle).toBeTypeOf("function");
    });

    it("clears all breakpoints on init", () => {
        breakpoints.toggle("main.asm", 5);
        init();
        expect(breakpoints.has("main.asm", 5)).toBe(false);
    });

    it("loads default source into editor", () => {
        expect(_editorSource).toContain("Hello World");
    });
});

// ── BP toggle callback ────────────────────────────────────────────

describe("BP toggle callback (gutter click simulation)", () => {
    it("adds a BP to main.asm", () => {
        _onBpToggle(10);
        expect(breakpoints.has("main.asm", 10)).toBe(true);
    });

    it("syncs CM editor state after toggle", () => {
        _onBpToggle(3);
        expect(_cmBps.has(3)).toBe(true);
    });

    it("removes BP on second toggle", () => {
        _onBpToggle(7);
        _onBpToggle(7);
        expect(breakpoints.has("main.asm", 7)).toBe(false);
        expect(_cmBps.has(7)).toBe(false);
    });

    it("multiple lines tracked independently", () => {
        _onBpToggle(1);
        _onBpToggle(5);
        _onBpToggle(1);
        expect(_cmBps).toEqual(new Set([5]));
        expect(breakpoints.getForFile("main.asm")).toEqual(new Set([5]));
    });
});

// ── saveCurrentTab / getMainSource ───────────────────────────────

describe("saveCurrentTab", () => {
    it("persists editor content to main.asm", () => {
        _editorSource = "MOV A, 1\nHLT";
        saveCurrentTab();
        expect(getMainSource()).toBe("MOV A, 1\nHLT");
    });
});

// ── getVirtualFiles ──────────────────────────────────────────────

describe("getVirtualFiles", () => {
    it("returns empty object when only main.asm exists", () => {
        expect(getVirtualFiles()).toEqual({});
    });
});

// ── switchTabForExec ─────────────────────────────────────────────

describe("switchTabForExec", () => {
    it("no-op when target is already active (main.asm)", () => {
        const before = _editorSource;
        switchTabForExec("main.asm");
        expect(_editorSource).toBe(before);
    });

    it("no-op when target file does not exist", () => {
        const before = _editorSource;
        switchTabForExec("nonexistent.asm");
        expect(_editorSource).toBe(before);
    });

    it("no-op does not corrupt CM BP state", () => {
        _onBpToggle(4); // main.asm line 4
        const bpsBefore = new Set(_cmBps);
        switchTabForExec("main.asm"); // no-op — already active
        expect(_cmBps).toEqual(bpsBefore);
    });
});

// ── checkFlat integration with breakpoints ───────────────────────

describe("checkFlat: BP check used by controls (end-to-end logic)", () => {
    it("single-file: BP at flatLine=5 is hit", () => {
        _onBpToggle(5); // sets BP at main.asm line 5
        expect(breakpoints.checkFlat(5, null)).toBe(true);
    });

    it("single-file: no BP at flatLine=6", () => {
        _onBpToggle(5);
        expect(breakpoints.checkFlat(6, null)).toBe(false);
    });

    it("multi-file: BP in included file resolved via lineMap", () => {
        const lineMap = new Map([
            [1, { file: null, line: 1 }],
            [2, { file: null, line: 2 }],
            [3, { file: "utils.asm", line: 1 }],
            [4, { file: "utils.asm", line: 2 }],
        ]);
        // Simulate: user clicked gutter in main.asm at line 2
        _onBpToggle(2); // toggle on active tab = main.asm
        // Simulate: user added utils.asm tab and set BP at line 1
        // (we can't switch tabs without DOM, so toggle directly)
        breakpoints.toggle("utils.asm", 1);

        expect(breakpoints.checkFlat(1, lineMap)).toBe(false); // main line 1, no BP
        expect(breakpoints.checkFlat(2, lineMap)).toBe(true); // main line 2, BP ✓
        expect(breakpoints.checkFlat(3, lineMap)).toBe(true); // utils line 1, BP ✓
        expect(breakpoints.checkFlat(4, lineMap)).toBe(false); // utils line 2, no BP
    });

    it("undefined flatLine never hits", () => {
        _onBpToggle(1);
        expect(breakpoints.checkFlat(undefined, null)).toBe(false);
    });
});
