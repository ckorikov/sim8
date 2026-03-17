/**
 * Tests for Phase 0 @include preprocessor in asm.js.
 */

import { describe, it, expect, vi, afterEach } from "vitest";
import { assemble, assembleAsync, AsmError } from "../lib/asm.js";

// ── Helpers ──────────────────────────────────────────────────────────

function asmOk(source, files = {}) {
    return assemble(source, 2, files);
}

function asmError(source, files = {}) {
    try {
        assemble(source, 2, files);
    } catch (e) {
        expect(e).toBeInstanceOf(AsmError);
        return e;
    }
    throw new Error("expected AsmError but none was thrown");
}

function stubFetch(arrayBuffer) {
    vi.stubGlobal(
        "fetch",
        vi.fn().mockResolvedValue({
            ok: true,
            arrayBuffer: () => Promise.resolve(arrayBuffer),
        }),
    );
}

// ── Tests ─────────────────────────────────────────────────────────────

describe("@include preprocessor", () => {
    it("basic include: included file label is visible in main", () => {
        const files = { "lib/print.asm": "print: RET" };
        const { labels } = asmOk('JMP start\nstart: CALL print\nHLT\n@include "lib/print.asm"', files);
        expect(labels).toHaveProperty("print");
        expect(labels).toHaveProperty("start");
    });

    it("nested includes: lib/a.asm includes lib/b.asm", () => {
        const files = {
            "lib/a.asm": '@include "lib/b.asm"\nhelper: RET',
            "lib/b.asm": "util: RET",
        };
        const { labels } = asmOk('@include "lib/a.asm"\nHLT', files);
        expect(labels).toHaveProperty("helper");
        expect(labels).toHaveProperty("util");
    });

    it('circular include → AsmError mentioning "circular include"', () => {
        const files = {
            "a.asm": '@include "b.asm"',
            "b.asm": '@include "a.asm"',
        };
        const err = asmError('@include "a.asm"', files);
        expect(err.message).toMatch(/circular include/i);
    });

    it('file not found → AsmError mentioning "file not found"', () => {
        const err = asmError('@include "missing.asm"', {});
        expect(err.message).toMatch(/file not found/i);
    });

    it('invalid syntax (missing quotes) → AsmError mentioning "invalid syntax"', () => {
        const err = asmError("@include lib/print.asm", {});
        expect(err.message).toMatch(/invalid syntax/i);
    });

    it('max include depth exceeded → AsmError mentioning "max include depth exceeded"', () => {
        // Build a chain: depth0.asm → depth1.asm → ... → depth16.asm → depth17.asm
        // The root source includes depth0.asm, so depth counter starts at 1 when
        // processing depth0.asm. A chain of 17 files exceeds the limit of 16.
        const files = {};
        for (let i = 0; i < 17; i++) {
            files[`depth${i}.asm`] = `@include "depth${i + 1}.asm"`;
        }
        files["depth17.asm"] = "HLT";
        const err = asmError('@include "depth0.asm"', files);
        expect(err.message).toMatch(/max include depth exceeded/i);
    });

    it("case-insensitive: @INCLUDE works the same as @include", () => {
        const files = { "lib/util.asm": "util: RET" };
        const { labels } = asmOk('@INCLUDE "lib/util.asm"\nHLT', files);
        expect(labels).toHaveProperty("util");
    });

    it("backward compat: assemble(source) without files arg still works", () => {
        const { code } = assemble("HLT");
        expect(code).toHaveLength(1);
    });

    // ── Multiple includes ────────────────────────────────────────

    it("multiple @include in one file: both labels visible", () => {
        const files = { "a.asm": "sub_a: RET", "b.asm": "sub_b: RET" };
        const { labels } = asmOk('@include "a.asm"\n@include "b.asm"\nHLT', files);
        expect(labels).toHaveProperty("sub_a");
        expect(labels).toHaveProperty("sub_b");
    });

    // ── Empty / comment-only included file ───────────────────────

    it("empty included file: no error, code continues", () => {
        const files = { "empty.asm": "" };
        const { code } = asmOk('@include "empty.asm"\nHLT', files);
        expect(code).toHaveLength(1);
    });

    it("included file with only comments: no error", () => {
        const files = { "comments.asm": "; just a comment\n; another" };
        const { code } = asmOk('@include "comments.asm"\nHLT', files);
        expect(code).toHaveLength(1);
    });

    // ── Leading whitespace ───────────────────────────────────────

    it("indented @include is accepted", () => {
        const files = { "util.asm": "util: RET" };
        const { labels } = asmOk('    @include "util.asm"\nHLT', files);
        expect(labels).toHaveProperty("util");
    });

    it("tab-indented @include is accepted", () => {
        const files = { "util.asm": "util: RET" };
        const { labels } = asmOk('\t@include "util.asm"\nHLT', files);
        expect(labels).toHaveProperty("util");
    });

    // ── No trailing newline ──────────────────────────────────────

    it("included file without trailing newline: label still assembled", () => {
        const files = { "notrail.asm": "sub: RET" }; // no trailing \n
        const { labels } = asmOk('@include "notrail.asm"\nHLT', files);
        expect(labels).toHaveProperty("sub");
    });

    // ── Forward reference ────────────────────────────────────────

    it("forward reference: main calls label defined in @include below", () => {
        const files = { "lib.asm": "myfn: RET" };
        const { labels } = asmOk('CALL myfn\nHLT\n@include "lib.asm"', files);
        expect(labels).toHaveProperty("myfn");
    });

    // ── Duplicate label ──────────────────────────────────────────

    it("duplicate label across main and included file → AsmError with filename of included file", () => {
        const files = { "dup.asm": "lbl: RET" };
        // Preprocessor merges both; assembler detects the duplicate label in the included file
        const err = asmError('lbl: HLT\n@include "dup.asm"', files);
        expect(err.message).toMatch(/duplicate label/i);
        expect(err.filename).toBe("dup.asm");
    });

    // ── AsmError filename field ──────────────────────────────────

    it("AsmError from included file carries filename", () => {
        const files = { "bad.asm": "INVALID_OP" };
        const err = asmError('@include "bad.asm"', files);
        expect(err.filename).toBe("bad.asm");
    });

    it("AsmError from root file has null filename", () => {
        const err = asmError("INVALID_OP", {});
        expect(err.filename).toBeNull();
    });

    // ── Malformed @include syntax variants ──────────────────────

    it("@include without quotes → invalid syntax", () => {
        const err = asmError("@include lib/foo.asm", {});
        expect(err.message).toMatch(/invalid syntax/i);
    });

    it("@include with only opening quote → invalid syntax", () => {
        const err = asmError('@include "lib/foo.asm', {});
        expect(err.message).toMatch(/invalid syntax/i);
    });

    it("@include with empty path string → invalid syntax", () => {
        const err = asmError('@include ""', {});
        expect(err.message).toMatch(/invalid syntax/i);
    });

    it("@include with trailing content → invalid syntax", () => {
        const err = asmError('@include "lib.asm" ; comment', {});
        expect(err.message).toMatch(/invalid syntax/i);
    });
});

describe("@include binary files (spec §5.8)", () => {
    it("Uint8Array: bytes are embedded as DB data", () => {
        const blob = new Uint8Array([0x01, 0x02, 0x03]);
        const { code } = asmOk('HLT\n@include "blob.bin"', { "blob.bin": blob });
        // HLT = 1 byte; then DB 1, 2, 3
        expect(Array.from(code.slice(1))).toEqual([0x01, 0x02, 0x03]);
    });

    it("ArrayBuffer: bytes are embedded as DB data", () => {
        const buf = new Uint8Array([0xab, 0xcd]).buffer;
        const { code } = asmOk('HLT\n@include "blob.bin"', { "blob.bin": buf });
        expect(code[1]).toBe(0xab);
        expect(code[2]).toBe(0xcd);
    });

    it("empty Uint8Array is silently skipped", () => {
        const empty = new Uint8Array(0);
        const { code: with_empty } = asmOk('HLT\n@include "empty.bin"', { "empty.bin": empty });
        const { code: without } = asmOk("HLT", {});
        expect(Array.from(with_empty)).toEqual(Array.from(without));
    });

    it("binary lineMap refers to @include directive location", () => {
        const blob = new Uint8Array([0xff]);
        const { lineMap } = asmOk('MOV A, 1\n@include "b.bin"\nHLT', { "b.bin": blob });
        // flat line 2 = the DB directive emitted for the binary include
        // must map back to the @include line in the root file (line 2)
        expect(lineMap.get(2)).toEqual({ file: null, line: 2 });
    });

    it("binary does not scan for nested @include directives", () => {
        // Content that looks like an @include — must not trigger recursive processing
        const fakeInclude = new TextEncoder().encode('@include "missing.asm"');
        // "missing.asm" is NOT in files — if recursion happened this would throw
        const { code } = asmOk('HLT\n@include "tricky.bin"', { "tricky.bin": fakeInclude });
        expect(code.length).toBeGreaterThan(1); // bytes were embedded, no error
    });
});

describe("@include URL (assembleAsync, spec §5.8)", () => {
    afterEach(() => vi.restoreAllMocks());

    it("text URL: label from remote file is visible", async () => {
        stubFetch(new TextEncoder().encode("urlsub: RET\n").buffer);
        const { labels } = await assembleAsync('CALL urlsub\nHLT\n@include "https://example.com/lib.asm"');
        expect(labels).toHaveProperty("urlsub");
    });

    it("binary URL: bytes embedded as DB data", async () => {
        stubFetch(new Uint8Array([0xde, 0xad, 0xbe]).buffer);
        const { code } = await assembleAsync('HLT\n@include "https://example.com/blob.bin"');
        expect(Array.from(code.slice(1))).toEqual([0xde, 0xad, 0xbe]);
    });

    it("HTTP error → AsmError with fetch failed", async () => {
        vi.stubGlobal(
            "fetch",
            vi.fn().mockResolvedValue({
                ok: false,
                status: 404,
            }),
        );
        await expect(assembleAsync('@include "https://example.com/missing.asm"')).rejects.toMatchObject({
            message: /fetch failed/i,
        });
    });

    it("network failure → AsmError with fetch failed", async () => {
        vi.stubGlobal("fetch", vi.fn().mockRejectedValue(new TypeError("Network error")));
        await expect(assembleAsync('@include "https://example.com/offline.asm"')).rejects.toMatchObject({
            message: /fetch failed/i,
        });
    });

    it("URL pre-provided in files dict is used directly (no fetch)", async () => {
        const fetchSpy = vi.fn();
        vi.stubGlobal("fetch", fetchSpy);
        const files = { "https://example.com/lib.asm": "provided: RET" };
        const { labels } = await assembleAsync('CALL provided\nHLT\n@include "https://example.com/lib.asm"', 2, files);
        expect(labels).toHaveProperty("provided");
        expect(fetchSpy).not.toHaveBeenCalled();
    });

    it("backward compat: assemble() without URL still works synchronously", () => {
        const { code } = assemble("HLT");
        expect(code).toHaveLength(1);
    });
});

// ── @page + @include interaction ─────────────────────────────────────

describe("@page + @include interaction", () => {
    it("@include after @page emits to that page", () => {
        const files = { "data.asm": "DB 10, 20, 30" };
        const { code } = asmOk('HLT\n@page 1\n@include "data.asm"', files);
        expect(code[256]).toBe(10);
        expect(code[257]).toBe(20);
        expect(code[258]).toBe(30);
    });

    it("label from @include on page 1 has correct address", () => {
        const files = { "lib.asm": "table: DB 42" };
        const { labels } = asmOk('HLT\n@page 1\n@include "lib.asm"', files);
        expect(labels.table).toBe(256); // page 1, offset 0
    });

    it("@page directive inside included file switches page", () => {
        const files = { "pages.asm": "@page 2\nDB 99" };
        const { code } = asmOk('HLT\n@page 1\nDB 1\n@include "pages.asm"', files);
        expect(code[256]).toBe(1); // page 1
        expect(code[512]).toBe(99); // page 2
    });
});

// ── No include guards ────────────────────────────────────────────────

describe("no include guards", () => {
    it("double include with label → duplicate label error", () => {
        const files = { "lib.asm": "helper: RET" };
        const err = asmError('@include "lib.asm"\n@include "lib.asm"\nHLT', files);
        expect(err.message).toMatch(/duplicate label/i);
    });

    it("double include without labels → data duplicated", () => {
        const files = { "data.asm": "DB 1, 2" };
        const { code } = asmOk('@include "data.asm"\n@include "data.asm"\nHLT', files);
        expect(Array.from(code.slice(0, 4))).toEqual([1, 2, 1, 2]);
    });
});

// ── Additional spec coverage ─────────────────────────────────────────

describe("additional @include spec coverage", () => {
    it("max depth 16 passes", () => {
        const files = {};
        for (let i = 0; i < 15; i++) {
            files[`depth${i}.asm`] = `@include "depth${i + 1}.asm"`;
        }
        files["depth15.asm"] = "HLT";
        const { code } = asmOk('@include "depth0.asm"', files);
        expect(code).toContain(0); // HLT
    });

    it("error in included file carries line number", () => {
        const files = { "bad.asm": "MOV A, 1\nINVALID_OP" };
        const err = asmError('@include "bad.asm"', files);
        expect(err.line).toBe(2);
    });
});
