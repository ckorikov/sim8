/**
 * Three-phase assembler for sim8 ISA v3: preprocessing (@include) + two-pass assembly.
 * Parsing lives in asm-parse.js; this module handles codegen and assembly passes.
 */

import { PAGE_SIZE, IO_START } from "./core.js";

import {
    // ISA symbols (re-exported by asm-parse from isa.js)
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    MNEMONICS_FP,
    FP_CONTROL_MNEMONICS,
    // Parser exports
    AsmError,
    parseLines as _parseLines,
    TAG_LABEL,
    TAG_ADDR_LABEL,
    TAG_FP_REG,
    TAG_FP_IMM,
    TAG_PAGE_LABEL,
    MNEMONICS_VU,
    RE_INCLUDE_FULL,
    RE_INCLUDE_START,
    isUrl,
    decodeUtf8,
} from "./asm-parse.js";

import { _encodeOperand, _findInstr } from "./asm-core.js";
import { _encodeDb, _encodeFpInstruction, _encodeFmovImm } from "./asm-fp.js";
import { _encodeVuInstr, _filterByTag } from "./asm-vu.js";

// Re-export for external consumers
export { AsmError };

// ── Instruction encoding ─────────────────────────────────────────

function _encodeInstruction(mnemonic, operands, line, dstSuffix, srcSuffix, arch, pline) {
    if (mnemonic === "DB") {
        return _encodeDb(operands, line);
    }

    if (arch >= 3 && MNEMONICS_VU.has(mnemonic)) {
        const suffixes = [pline.vuFmtSuffix, pline.vuModeSuffix, pline.vuCondSuffix].filter((s) => s !== null);
        return _encodeVuInstr(mnemonic, suffixes, operands, line);
    }

    if (arch >= 2 && MNEMONICS_FP.has(mnemonic)) {
        // FMOV immediate special case
        if (mnemonic === "FMOV" && operands.length === 2 && operands[1].tag === TAG_FP_IMM) {
            return _encodeFmovImm(operands, dstSuffix, line);
        }

        const instr = _findInstr(mnemonic, operands, line, BY_MNEMONIC_FP);
        if (FP_CONTROL_MNEMONICS.has(mnemonic)) {
            return [instr.op, ...operands.map((op) => _encodeOperand(op))];
        }
        return _encodeFpInstruction(instr, operands, dstSuffix, srcSuffix, line);
    }

    const instr = _findInstr(mnemonic, operands, line, BY_MNEMONIC);
    return [instr.op, ...operands.map((op) => _encodeOperand(op))];
}

// ── Phase 0: @include preprocessing ──────────────────────────────

const _MAX_INCLUDE_DEPTH = 16;
const _RE_PAGE_NUM = /^\s*@page\s+(\d+)/i;

/** Find the most recent @page number from emitted lines. */
function _findCurrentPage(outLines) {
    for (let i = outLines.length - 1; i >= 0; i--) {
        const m = _RE_PAGE_NUM.exec(outLines[i]);
        if (m) return parseInt(m[1], 10);
    }
    return 0;
}

/** Emit a line into outLines + lineMap. */
function _emitLine(text, outLines, lineMap, filename, lineNo) {
    const flatLineNo = outLines.length + 1;
    lineMap.set(flatLineNo, { file: filename, line: lineNo });
    outLines.push(text);
}

/** Embed binary data as DB directives, auto-splitting across pages if needed. */
function _embedBinary(bytes, outLines, lineMap, filename, lineNo) {
    if (bytes.length <= PAGE_SIZE) {
        _emitLine("DB " + Array.from(bytes).join(", "), outLines, lineMap, filename, lineNo);
        return;
    }
    let page = _findCurrentPage(outLines);
    for (let i = 0; i < bytes.length; i += PAGE_SIZE) {
        if (i > 0) {
            page++;
            if (page > 255) {
                throw new AsmError(
                    `@include: binary file spans beyond page 255 ` +
                        `(${bytes.length} bytes from page ${page - Math.floor(i / PAGE_SIZE)})`,
                    lineNo,
                    filename,
                );
            }
            _emitLine(`@page ${page}`, outLines, lineMap, filename, lineNo);
        }
        const chunk = bytes.slice(i, i + PAGE_SIZE);
        _emitLine("DB " + Array.from(chunk).join(", "), outLines, lineMap, filename, lineNo);
    }
}

/**
 * Collect lines from source into outLines, building lineMap (1-based flat line → {file, line}).
 * Mutates outLines and lineMap in place (mirrors Python's _collect pattern).
 */
function _collectLines(source, files, filename, visited, depth, outLines, lineMap) {
    const lines = source.split("\n");
    for (let i = 0; i < lines.length; i++) {
        const lineNo = i + 1;
        const text = lines[i];
        if (RE_INCLUDE_START.test(text)) {
            const m = RE_INCLUDE_FULL.exec(text);
            if (!m || !m[1]) {
                throw new AsmError("@include: invalid syntax", lineNo, filename);
            }
            const path = m[1];
            if (!(path in files)) {
                const msg = isUrl(path)
                    ? `@include: URL not pre-fetched (use assembleAsync): ${path}`
                    : `@include: file not found: ${path}`;
                throw new AsmError(msg, lineNo, filename);
            }
            if (visited.has(path)) {
                throw new AsmError(`@include: circular include: ${path}`, lineNo, filename);
            }
            if (depth >= _MAX_INCLUDE_DEPTH) {
                throw new AsmError("@include: max include depth exceeded", lineNo, filename);
            }
            const included = files[path];
            if (included instanceof Uint8Array || included instanceof ArrayBuffer) {
                // Binary file: embed raw bytes as DB directives, auto-splitting across pages.
                const bytes = included instanceof ArrayBuffer ? new Uint8Array(included) : included;
                if (bytes.length > 0) {
                    _embedBinary(bytes, outLines, lineMap, filename, lineNo);
                }
            } else {
                _collectLines(included, files, path, new Set([...visited, path]), depth + 1, outLines, lineMap);
            }
        } else {
            _emitLine(text, outLines, lineMap, filename, lineNo);
        }
    }
}

function _preprocess(source, files) {
    const outLines = [];
    const lineMap = new Map(); // flatLine (1-based) → { file: string|null, line: number }
    _collectLines(source, files, null, new Set(), 0, outLines, lineMap);
    return { flat: outLines.join("\n"), lineMap };
}

// ── Jump/call mnemonics (for cross-page validation) ──────────────

const _JUMP_MNEMONICS = new Set(["JMP", "JC", "JNC", "JZ", "JNZ", "JA", "JNA", "CALL"]);

// ── Two-pass assembly (pass 1 + pass 2) ──────────────────────────

function _pass1HandlePage(st, pline) {
    st.hasPageDirective = true;
    const pageNum = pline.operands[0].value;
    if (!st.seenPages.has(pageNum)) {
        st.seenPages.add(pageNum);
        st.pageCodes[pageNum] = [];
    }
    st.currentPage = pageNum;
    st.pageLocs[pageNum] = pline.lineNo;
    if (pline.operands.length > 1) {
        const targetOffset = pline.operands[1].value;
        const currentLen = st.pageCodes[pageNum].length;
        if (targetOffset < currentLen) {
            throw new AsmError(
                `@page ${pageNum}: offset ${targetOffset} is before current position ${currentLen}`,
                pline.lineNo,
            );
        }
        for (let i = currentLen; i < targetOffset; i++) {
            st.pageCodes[pageNum].push(0);
        }
    }
}

function _collectLabelPatches(operands, pline, pos, arch, page, isJump) {
    const patches = [];
    const isFpData = arch >= 2 && MNEMONICS_FP.has(pline.mnemonic) && !FP_CONTROL_MNEMONICS.has(pline.mnemonic);

    for (let i = 0; i < operands.length; i++) {
        const op = operands[i];
        if (op.tag !== TAG_LABEL && op.tag !== TAG_ADDR_LABEL && op.tag !== TAG_PAGE_LABEL) continue;
        const isPageRef = op.tag === TAG_PAGE_LABEL;
        const mk = (patchPos, ref = isPageRef) => ({
            page,
            pos: patchPos,
            name: op.name,
            isPageRef: ref,
            isJump,
            lineNo: pline.lineNo,
        });

        if (isFpData) {
            const fpCount = _filterByTag(operands, TAG_FP_REG).length;
            const nonFpIdx = operands.slice(0, i).filter((o) => o.tag !== TAG_FP_REG).length;
            patches.push(mk(pos + 1 + fpCount + nonFpIdx));
        } else if (pline.mnemonic === "VSET") {
            // 3-op [163, target, lo, hi]: i==1 → hi at pos+3, i==2 → lo at pos+2
            // 2-op bare label: auto-expand to full 16-bit — emit lo (pos+2) + hi (pos+3)
            // 2-op [165, target, addr]: addr always at pos+2
            if (operands.length === 3) {
                patches.push(mk(i === 1 ? pos + 3 : pos + 2));
            } else if (op.tag === TAG_LABEL) {
                patches.push(mk(pos + 2, false));
                patches.push(mk(pos + 3, true));
            } else {
                patches.push(mk(pos + 2));
            }
        } else {
            patches.push(mk(pos + 1 + i));
        }
    }
    return patches;
}

function _pass1(parsed, arch) {
    const st = {
        pageCodes: { 0: [] },
        currentPage: 0,
        seenPages: new Set([0]),
        hasPageDirective: false,
        pageLocs: {},
    };
    const labelInfo = {}; // name → { page, offset }
    const pageMapping = []; // [{ page, offset, lineNo }]
    const labelPatches = []; // [{ page, pos, name, isPageRef, isJump, lineNo }]

    for (const pline of parsed) {
        if (pline.label !== null) {
            const pos = st.pageCodes[st.currentPage].length;
            labelInfo[pline.label] = { page: st.currentPage, offset: pos };
        }

        if (pline.mnemonic === null) continue;

        if (pline.mnemonic === "@PAGE") {
            _pass1HandlePage(st, pline);
            continue;
        }

        const operands = pline.operands || [];
        const pos = st.pageCodes[st.currentPage].length;

        const encoded = _encodeInstruction(
            pline.mnemonic,
            operands,
            pline.lineNo,
            pline.dstSuffix,
            pline.srcSuffix,
            arch,
            pline,
        );

        if (pline.mnemonic !== "DB") {
            pageMapping.push({ page: st.currentPage, offset: pos, lineNo: pline.lineNo });
        }

        const isJump = _JUMP_MNEMONICS.has(pline.mnemonic);
        labelPatches.push(..._collectLabelPatches(operands, pline, pos, arch, st.currentPage, isJump));
        st.pageCodes[st.currentPage].push(...encoded);
    }

    return {
        pageCodes: st.pageCodes,
        hasPageDirective: st.hasPageDirective,
        labelInfo,
        pageLocs: st.pageLocs,
        pageMapping,
        labelPatches,
    };
}

function _checkPageOverflow(st, lineMap) {
    if (!st.hasPageDirective) return;
    for (const [page, data] of Object.entries(st.pageCodes)) {
        if (data.length > PAGE_SIZE) {
            const flatLine = st.pageLocs[page] || 1;
            const loc = lineMap?.get(flatLine);
            throw new AsmError(
                `Page ${page} overflow: ${data.length} bytes exceeds ${PAGE_SIZE}`,
                loc ? loc.line : flatLine,
                loc ? loc.file : null,
            );
        }
    }
    if (st.pageCodes[0] && st.pageCodes[0].length > IO_START) {
        console.warn(
            `Page 0 output is ${st.pageCodes[0].length} bytes; I/O region (${IO_START}-${PAGE_SIZE - 1}) will be overwritten`,
        );
    }
}

function _pass2(st) {
    for (const patch of st.labelPatches) {
        const { page: patchPage, pos: patchPos, name: labelName, isPageRef, isJump, lineNo } = patch;
        if (!(labelName in st.labelInfo)) {
            throw new AsmError(`Undefined label: ${labelName}`, lineNo);
        }
        const { page: labelPage, offset: labelOffset } = st.labelInfo[labelName];

        if (isPageRef) {
            st.pageCodes[patchPage][patchPos] = labelPage;
        } else {
            if (labelOffset < 0 || labelOffset > 255) {
                throw new AsmError(`${labelOffset} must have a value between 0-255`, lineNo);
            }
            if (isJump && labelPage !== patchPage) {
                if (patchPage === 0) {
                    throw new AsmError(
                        `jump target '${labelName}' is on page ${labelPage}, but IP executes only on page 0`,
                        lineNo,
                    );
                } else {
                    throw new AsmError(`cross-page jump from page ${patchPage} to page ${labelPage}`, lineNo);
                }
            }
            st.pageCodes[patchPage][patchPos] = labelOffset;
        }
    }
}

function _buildOutput(st) {
    const multi = st.hasPageDirective;

    // Flatten code
    let code;
    if (multi) {
        const maxPage = Math.max(...Object.keys(st.pageCodes).map(Number));
        code = new Array((maxPage + 1) * PAGE_SIZE).fill(0);
        for (const [page, data] of Object.entries(st.pageCodes)) {
            const base = Number(page) * PAGE_SIZE;
            for (let i = 0; i < data.length; i++) {
                code[base + i] = data[i];
            }
        }
    } else {
        code = st.pageCodes[0];
    }

    const flatAddr = (page, offset) => (multi ? page * PAGE_SIZE + offset : offset);

    // Labels: name → memory address
    const labels = {};
    for (const [name, info] of Object.entries(st.labelInfo)) {
        labels[name] = flatAddr(info.page, info.offset);
    }

    // Mapping: flat code position → lineNo
    const mapping = {};
    for (const entry of st.pageMapping) {
        mapping[flatAddr(entry.page, entry.offset)] = entry.lineNo;
    }

    return { code, labels, mapping };
}

export function assemble(source, arch = 2, files = {}) {
    // Phase 0: preprocessing
    const { flat, lineMap } = _preprocess(source, files);

    const _locErr = (e) => {
        if (e instanceof AsmError) {
            const loc = lineMap.get(e.line);
            if (loc) return new AsmError(e.message, loc.line, loc.file);
        }
        return e;
    };

    let parsed;
    try {
        parsed = _parseLines(flat, arch);
    } catch (e) {
        throw _locErr(e);
    }

    try {
        // Pass 1: generate code
        const st = _pass1(parsed, arch);
        // Page overflow check
        _checkPageOverflow(st, lineMap);
        // Pass 2: resolve labels
        _pass2(st);
        // Build output
        const { code, labels, mapping } = _buildOutput(st);
        return { code, labels, mapping, lineMap };
    } catch (e) {
        throw _locErr(e);
    }
}

// ── Async assembly with URL @include support ──────────────────────

async function _prefetchUrls(source, allFiles, visited, depth) {
    if (depth >= _MAX_INCLUDE_DEPTH) return;

    // Phase 1: scan — collect new URL includes with their line numbers
    const lines = source.split("\n");
    const urlLines = new Map(); // url → lineNo
    for (let i = 0; i < lines.length; i++) {
        const m = RE_INCLUDE_FULL.exec(lines[i]);
        if (!m || !isUrl(m[1]) || visited.has(m[1])) continue;
        visited.add(m[1]);
        urlLines.set(m[1], i + 1);
    }

    // Phase 2: fetch missing URLs in parallel
    await Promise.all(
        [...urlLines.entries()]
            .filter(([url]) => !(url in allFiles))
            .map(async ([url, lineNo]) => {
                try {
                    const resp = await fetch(url);
                    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
                    const bytes = new Uint8Array(await resp.arrayBuffer());
                    allFiles[url] = decodeUtf8(bytes) ?? bytes;
                } catch (e) {
                    throw new AsmError(`@include: fetch failed: ${url}: ${e.message}`, lineNo, null);
                }
            }),
    );

    // Phase 3: recurse into text files in parallel
    await Promise.all(
        [...urlLines.keys()]
            .filter((url) => typeof allFiles[url] === "string")
            .map((url) => _prefetchUrls(allFiles[url], allFiles, visited, depth + 1)),
    );
}

/**
 * Assemble with URL @include support. Fetches all URL includes before assembling.
 * Use this instead of assemble() when the source may contain @include "https://..." directives.
 */
export async function assembleAsync(source, arch = 2, files = {}) {
    const allFiles = { ...files };
    await _prefetchUrls(source, allFiles, new Set(), 0);
    return assemble(source, arch, allFiles);
}
