/**
 * Global breakpoint registry — single source of truth for all breakpoints
 * across editor tabs. Keyed by original filename (null = main file / single-file mode).
 *
 * Execution checking works in flat (preprocessed) space via checkFlat().
 */

export const MAIN_FILE = "main.asm";

/** @type {Map<string|null, Set<number>>} */
const _store = new Map();

function _key(file) {
    return file ?? MAIN_FILE;
}

export const breakpoints = {
    /** Toggle a breakpoint at the given original-file line. */
    toggle(file, line) {
        const key = _key(file);
        let set = _store.get(key);
        if (!set) {
            set = new Set();
            _store.set(key, set);
        }
        if (set.has(line)) set.delete(line);
        else set.add(line);
    },

    /** Returns true if a breakpoint exists at the given original-file line. */
    has(file, line) {
        return _store.get(_key(file))?.has(line) ?? false;
    },

    /** Returns the Set<lineNo> for a given file (never mutate the result). */
    getForFile(file) {
        return _store.get(_key(file)) ?? new Set();
    },

    /** Rename breakpoints from one file key to another (preserves BPs on tab rename). */
    renameFile(oldFile, newFile) {
        const key = _key(oldFile);
        const bps = _store.get(key);
        if (bps) {
            _store.delete(key);
            _store.set(_key(newFile), bps);
        }
    },

    /** Remove all breakpoints for a file (e.g. on tab close). */
    clearFile(file) {
        _store.delete(_key(file));
    },

    /** Remove all breakpoints across all files. */
    clearAll() {
        _store.clear();
    },

    /**
     * Check whether a flat (preprocessed) line number hits a breakpoint.
     * @param {number|undefined} flatLine - from asm.mapping[cpu.ip]
     * @param {Map<number, {file: string|null, line: number}>|null} lineMap - from asm.lineMap
     */
    checkFlat(flatLine, lineMap) {
        if (flatLine === undefined) return false;
        const loc = lineMap?.get(flatLine);
        const file = loc?.file ?? null;
        const line = loc?.line ?? flatLine;
        return this.has(file, line);
    },
};
