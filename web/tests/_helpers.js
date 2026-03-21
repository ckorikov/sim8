/**
 * Shared test helpers for assembler tests.
 */

import { expect } from "vitest";
import { assemble, AsmError } from "../lib/asm.js";

/** Shorthand: assemble and return just the code bytes. */
export function asm(source, arch = 2) {
    return assemble(source, arch).code;
}

/** Shorthand: assemble and return label table. */
export function labels(source, arch = 2) {
    return assemble(source, arch).labels;
}

/** Shorthand: assemble expecting AsmError, return the error. */
export function asmError(source, arch = 2) {
    let caught;
    try {
        assemble(source, arch);
    } catch (e) {
        caught = e;
    }
    expect(caught).toBeInstanceOf(AsmError);
    return caught;
}
