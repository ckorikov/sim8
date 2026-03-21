import { describe, it, expect } from "vitest";
import { renderHex } from "../src/hexview.js";

describe("renderHex", () => {
    it("returns empty string for empty input", () => {
        expect(renderHex(new Uint8Array(0))).toBe("");
    });

    it("formats a single byte — offset, hex, ASCII", () => {
        const result = renderHex(new Uint8Array([0x41])); // 'A'
        expect(result).toMatch(/^0000/);
        expect(result).toContain("41");
        expect(result).toMatch(/A\s*$/);
    });

    it("shows dot for non-printable bytes", () => {
        const result = renderHex(new Uint8Array([0x00, 0x01, 0x7f]));
        // ASCII column should be all dots
        expect(result).toMatch(/\.\.\./);
    });

    it("shows printable ASCII in ASCII column", () => {
        const bytes = new Uint8Array([0x48, 0x65, 0x6c, 0x6c, 0x6f]); // "Hello"
        const result = renderHex(bytes);
        expect(result).toContain("Hello");
    });

    it("wraps at 16 bytes — produces two rows for 17 bytes", () => {
        const bytes = new Uint8Array(17);
        const lines = renderHex(bytes).split("\n");
        expect(lines).toHaveLength(2);
    });

    it("encodes row offsets in hex", () => {
        const bytes = new Uint8Array(32);
        const lines = renderHex(bytes).split("\n");
        expect(lines[0]).toMatch(/^0000/);
        expect(lines[1]).toMatch(/^0010/);
    });

    it("pads partial last row with spaces", () => {
        // 17 bytes: second row has only 1 byte
        const bytes = new Uint8Array(17).fill(0x41);
        const lines = renderHex(bytes).split("\n");
        expect(lines).toHaveLength(2);
        // Second row hex section should be padded (lots of spaces after "41")
        const hexSection = lines[1].slice(6, 6 + 8 * 3 - 1);
        expect(hexSection.trimEnd()).toBe("41");
    });

    it("exactly 16 bytes produces one row", () => {
        const bytes = new Uint8Array(16).fill(0xff);
        const lines = renderHex(bytes).split("\n");
        expect(lines).toHaveLength(1);
        expect(lines[0]).toMatch(/^0000/);
    });

    it("large offset uses 4 hex digits", () => {
        const bytes = new Uint8Array(0x100 + 1); // 257 bytes → offset 0x100 on row 17
        const lines = renderHex(bytes).split("\n");
        expect(lines[lines.length - 1]).toMatch(/^0100/);
    });

    it("space 0x20 and tilde 0x7e are printable; DEL 0x7f is dot", () => {
        const result = renderHex(new Uint8Array([0x20, 0x7e, 0x7f]));
        const asciiCol = result.slice(-16).trimEnd();
        // 0x20=' ', 0x7e='~', 0x7f='.'
        expect(asciiCol).toContain(" ");
        expect(asciiCol).toContain("~");
        expect(asciiCol).toContain(".");
    });
});
