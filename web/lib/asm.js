/**
 * Three-phase assembler for sim8 ISA v3: preprocessing (@include) + two-pass assembly.
 * Parsing lives in asm-parse.js; this module handles codegen and assembly passes.
 */

import { floatToBytes } from "./fp.js";
import { PAGE_SIZE, IO_START } from "./core.js";

import {
    VU_SUFFIX_TO_FMT,
    VU_SUFFIX_TO_MODE,
    VU_CMP_SUFFIX,
    VU_FMT_ELEM_SIZE,
    VU_MODE_VV,
    VU_MODE_VS,
    VU_MODE_VI,
    VU_MODE_R,
    VU_SYNC_MNEMONICS,
    encodeVfm,
    encodeVuRegs,
} from "./isa.js";

import {
    // ISA symbols (re-exported by asm-parse from isa.js)
    Op,
    OpType,
    BY_MNEMONIC,
    BY_MNEMONIC_FP,
    MNEMONICS_FP,
    FP_CONTROL_MNEMONICS,
    GPR_CODES,
    ARITH_CODES,
    STACK_CODES,
    FP_SUFFIX_TO_FMT,
    FP_FMT_WIDTH,
    FP_WIDTH_REGS,
    FP_FMT_O3,
    encodeRegaddr,
    encodeFpm,
    // Parser exports
    AsmError,
    parseLines as _parseLines,
    TAG_REG,
    TAG_CONST,
    TAG_ADDR,
    TAG_REGADDR,
    TAG_STRING,
    TAG_LABEL,
    TAG_ADDR_LABEL,
    TAG_FP_REG,
    TAG_FLOAT,
    TAG_FP_IMM,
    TAG_PAGE_LABEL,
    TAG_VU_REG,
    MNEMONICS_VU,
    RE_INCLUDE_FULL,
    RE_INCLUDE_START,
    isUrl,
    decodeUtf8,
} from "./asm-parse.js";

// Re-export for external consumers
export { AsmError };

// ── Operand matching ─────────────────────────────────────────────

function _operandMatches(op, ot) {
    switch (ot) {
        case OpType.REG:
            return op.tag === TAG_REG;
        case OpType.REG_ARITH:
            return op.tag === TAG_REG && ARITH_CODES.has(op.code);
        case OpType.REG_GPR:
            return op.tag === TAG_REG && GPR_CODES.has(op.code);
        case OpType.REG_STACK:
            return op.tag === TAG_REG && STACK_CODES.has(op.code);
        case OpType.IMM:
            return op.tag === TAG_CONST || op.tag === TAG_LABEL || op.tag === TAG_PAGE_LABEL;
        case OpType.MEM:
            return op.tag === TAG_ADDR || op.tag === TAG_ADDR_LABEL;
        case OpType.REGADDR:
            return op.tag === TAG_REGADDR;
        case OpType.FP_REG:
            return op.tag === TAG_FP_REG;
        case OpType.FP_IMM8:
        case OpType.FP_IMM16:
            return op.tag === TAG_FP_IMM;
        default:
            return false;
    }
}

// ── Operand encoding ─────────────────────────────────────────────

function _encodeOperand(op) {
    switch (op.tag) {
        case TAG_REG:
            return op.code;
        case TAG_CONST:
            return op.value;
        case TAG_ADDR:
            return op.value;
        case TAG_REGADDR:
            return encodeRegaddr(op.regCode, op.offset);
        case TAG_LABEL:
            return 0; // placeholder for pass 2
        case TAG_ADDR_LABEL:
            return 0; // placeholder for pass 2
        case TAG_PAGE_LABEL:
            return 0; // placeholder for pass 2
        default:
            throw new Error(`unexpected operand: ${op.tag}`);
    }
}

// ── Instruction matching ─────────────────────────────────────────

function _findInstr(mnemonic, operands, line, table = BY_MNEMONIC) {
    const candidates = table[mnemonic];
    if (!candidates) {
        throw new AsmError(`Invalid instruction: ${mnemonic}`, line);
    }

    for (const instr of candidates) {
        if (instr.sig.length !== operands.length) continue;
        if (instr.sig.every((ot, i) => _operandMatches(operands[i], ot))) return instr;
    }

    const maxArity = Math.max(...candidates.map((i) => i.sig.length));
    if (operands.length > maxArity) {
        throw new AsmError(`${mnemonic}: too many arguments`, line);
    }
    throw new AsmError(`${mnemonic} does not support this operand(s)`, line);
}

// ── FP float encoding helper ─────────────────────────────────────

function _encodeFloat(value, fmt, line) {
    const { data, exc } = floatToBytes(value, fmt);
    if (exc.overflow && fmt === FP_FMT_O3) {
        throw new AsmError("Float value out of range for format E4M3", line);
    }
    return data;
}

// ── DB encoding ──────────────────────────────────────────────────

function _encodeDbOperand(op, line, result) {
    if (op.tag === TAG_CONST) {
        result.push(op.value);
        return;
    }
    if (op.tag === TAG_STRING) {
        if (!op.text) {
            throw new AsmError("DB string must not be empty", line);
        }
        for (const c of op.text) result.push(c.charCodeAt(0));
        return;
    }
    if (op.tag === TAG_FLOAT) {
        result.push(..._encodeFloat(op.value, op.fmt, line));
        return;
    }
    throw new AsmError("DB does not support this operand", line);
}

function _encodeDb(operands, line) {
    const result = [];
    for (const op of operands) {
        _encodeDbOperand(op, line, result);
    }
    return result;
}

// ── FP suffix validation ─────────────────────────────────────────

function _validateFpSuffix(suffix, line) {
    const upper = suffix.toUpperCase();
    if (!(upper in FP_SUFFIX_TO_FMT)) {
        throw new AsmError(`Invalid FP format suffix: .${suffix}`, line);
    }
    return FP_SUFFIX_TO_FMT[upper];
}

function _validateFpRegWidth(reg, fmt, line) {
    const fmtWidth = FP_FMT_WIDTH[fmt];
    const allowed = FP_WIDTH_REGS[fmtWidth];
    if (!allowed || !allowed.has(reg.name)) {
        throw new AsmError("FP format suffix does not match register width", line);
    }
}

// ── FP instruction encoding ──────────────────────────────────────

function _encodeFpInstruction(instr, operands, dstSuffix, srcSuffix, line) {
    const dstFmt = dstSuffix ? _validateFpSuffix(dstSuffix, line) : null;
    const srcFmt = srcSuffix ? _validateFpSuffix(srcSuffix, line) : null;

    // FCVT special case: dual suffix
    if (instr.op === Op.FCVT_FP_FP) {
        if (dstFmt === srcFmt) {
            throw new AsmError("FCVT with identical formats (use FMOV)", line);
        }
        const dstReg = operands[0];
        const srcReg = operands[1];
        _validateFpRegWidth(dstReg, dstFmt, line);
        _validateFpRegWidth(srcReg, srcFmt, line);
        const dstFpm = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);
        const srcFpm = encodeFpm(srcReg.phys, srcReg.pos, srcFmt);
        return [instr.op, dstFpm, srcFpm];
    }

    const fpOps = [];
    const nonFpOps = [];
    for (const op of operands) {
        if (op.tag === TAG_FP_REG) {
            _validateFpRegWidth(op, dstFmt, line);
            fpOps.push(op);
        } else {
            nonFpOps.push(op);
        }
    }

    const fpmBytes = fpOps.map((fp) => encodeFpm(fp.phys, fp.pos, dstFmt));
    const nonFpBytes = nonFpOps.map((op) => _encodeOperand(op));

    return [instr.op, ...fpmBytes, ...nonFpBytes];
}

// ── FMOV immediate encoding ─────────────────────────────────────

function _encodeFmovImm(operands, dstSuffix, line) {
    if (operands[0].tag !== TAG_FP_REG) {
        throw new AsmError("FMOV does not support this operand(s)", line);
    }

    const dstReg = operands[0];
    const fpImm = operands[1];
    const dstFmt = _validateFpSuffix(dstSuffix, line);
    const fmtWidth = FP_FMT_WIDTH[dstFmt];

    if (fmtWidth === 32) {
        throw new AsmError("FP immediate not supported for float32", line);
    }
    if (fmtWidth === 4) {
        throw new AsmError("FP immediate not supported for 4-bit formats", line);
    }

    // Check literal suffix matches instruction suffix
    if (fpImm.fmt !== null && fpImm.fmt !== dstFmt) {
        throw new AsmError("FP immediate suffix mismatch", line);
    }

    _validateFpRegWidth(dstReg, dstFmt, line);

    const data = _encodeFloat(fpImm.value, dstFmt, line);
    const fpmByte = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);

    if (fmtWidth === 8) {
        return [Op.FMOV_FP_IMM8, fpmByte, data[0]];
    }
    return [Op.FMOV_FP_IMM16, fpmByte, data[0], data[1]];
}

// ── VU instruction encoding ──────────────────────────────────────

function _encodeVuInstr(mnemonic, suffixes, operands, line) {
    if (VU_SYNC_MNEMONICS.has(mnemonic)) {
        return _encodeVuSync(mnemonic, operands, line);
    }
    return _encodeVuAsync(mnemonic, suffixes, operands, line);
}

function _encodeVuSync(mnemonic, operands, line) {
    if (mnemonic === "VFCLR") return [Op.VFCLR];
    if (mnemonic === "VWAIT") return [Op.VWAIT];
    if (mnemonic === "VFSTAT") {
        if (operands.length !== 1 || operands[0].tag !== TAG_REG) {
            throw new AsmError("VFSTAT requires one GPR operand", line);
        }
        if (operands[0].code > 3) {
            throw new AsmError("VFSTAT requires GPR A-D", line);
        }
        return [Op.VFSTAT, operands[0].code];
    }
    if (mnemonic === "VSET") return _encodeVset(operands, line);
    throw new AsmError(`Unknown VU sync instruction: ${mnemonic}`, line);
}

function _encodeVset(operands, line) {
    if (operands.length < 2) {
        throw new AsmError("VSET requires at least 2 operands", line);
    }
    if (operands[0].tag !== TAG_VU_REG) {
        throw new AsmError("VSET first operand must be a VU register", line);
    }
    const target = operands[0].code;

    // VSET vreg, imm16 (opcode 163)
    if (operands[1].tag === TAG_CONST && operands.length === 2) {
        const val = operands[1].value;
        if (val < 0 || val > 65535) {
            throw new AsmError(`VSET immediate must be 0-65535, got ${val}`, line);
        }
        return [Op.VSET_IMM16, target, val & 0xff, (val >> 8) & 0xff];
    }

    // VSET vreg, {label}, label (opcode 163) — page + offset as two standard patches
    if (
        operands.length === 3 &&
        operands[1].tag === TAG_PAGE_LABEL &&
        (operands[2].tag === TAG_LABEL || operands[2].tag === TAG_CONST)
    ) {
        const loVal = operands[2].tag === TAG_CONST ? operands[2].value : 0;
        return [Op.VSET_IMM16, target, loVal, 0];
    }

    // VSET vreg, rH, rL (opcode 164)
    if (operands.length === 3 && operands[1].tag === TAG_REG && operands[2].tag === TAG_REG) {
        const rH = operands[1].code;
        const rL = operands[2].code;
        if (rH > 3 || rL > 3) {
            throw new AsmError("VSET GPR pair requires A-D", line);
        }
        return [Op.VSET_GPR, target, (rH << 2) | rL];
    }

    // VSET vreg, [addr] / [label] (opcode 165)
    if (operands[1].tag === TAG_ADDR || operands[1].tag === TAG_ADDR_LABEL) {
        const addr = operands[1].tag === TAG_ADDR ? operands[1].value : 0;
        return [Op.VSET_MEM, target, addr];
    }

    // VSET vreg, [reg+-offset] (opcode 166)
    if (operands[1].tag === TAG_REGADDR) {
        return [Op.VSET_MEMI, target, encodeRegaddr(operands[1].regCode, operands[1].offset)];
    }

    throw new AsmError("VSET does not support this operand(s)", line);
}

const _VU_MNEMONIC_TO_OP = {
    VADD: Op.VADD,
    VSUB: Op.VSUB,
    VMUL: Op.VMUL,
    VDIV: Op.VDIV,
    VMAX: Op.VMAX,
    VMIN: Op.VMIN,
    VDOT: Op.VDOT,
    VSQRT: Op.VSQRT,
    VNEG: Op.VNEG,
    VABS: Op.VABS,
    VCMP: Op.VCMP,
    VSEL: Op.VSEL,
    VMOV: Op.VMOV,
    VFILL: Op.VFILL,
};

const _VU_SINGLE_MODE = new Set(["VDOT", "VSQRT", "VNEG", "VABS", "VSEL", "VMOV"]);

function _resolveVuModeCond(mnemonic, modeSuffix, operands, line) {
    if (mnemonic === "VCMP") {
        if (modeSuffix === null) {
            throw new AsmError("VCMP requires a condition suffix", line);
        }
        const condUpper = modeSuffix.toUpperCase();
        if (!(condUpper in VU_CMP_SUFFIX)) {
            throw new AsmError(`Invalid VCMP condition: .${modeSuffix}`, line);
        }
        return [VU_MODE_VV, VU_CMP_SUFFIX[condUpper]];
    }
    if (mnemonic === "VFILL") return [VU_MODE_VI, 0];
    if (_VU_SINGLE_MODE.has(mnemonic)) return [0, 0];

    // Explicit suffix takes priority
    if (modeSuffix !== null) {
        const modeUpper = modeSuffix.toUpperCase();
        if (!(modeUpper in VU_SUFFIX_TO_MODE)) {
            throw new AsmError(`Invalid VU mode suffix: .${modeSuffix}`, line);
        }
        return [VU_SUFFIX_TO_MODE[modeUpper], 0];
    }

    // Infer from operands
    const hasGpr = operands.some((op) => op.tag === TAG_REG);
    const hasImm = operands.some((op) => op.tag === TAG_CONST);
    const vuCount = operands.filter((op) => op.tag === TAG_VU_REG).length;
    if (hasGpr) return [VU_MODE_VS, 0];
    if (hasImm) return [VU_MODE_VI, 0];
    if (vuCount <= 2) return [VU_MODE_R, 0];
    return [VU_MODE_VV, 0];
}

function _resolveVuFmt(mnemonic, fmtSuffix, line) {
    if (fmtSuffix === null) {
        throw new AsmError(`${mnemonic} requires a format suffix`, line);
    }
    const upper = fmtSuffix.toUpperCase();
    if (!(upper in VU_SUFFIX_TO_FMT)) {
        throw new AsmError(`Invalid VU format suffix: .${fmtSuffix}`, line);
    }
    return VU_SUFFIX_TO_FMT[upper];
}

function _encodeVuRegsFromOperands(operands, mnemonic, mode, line) {
    const vuRegs = operands.filter((op) => op.tag === TAG_VU_REG);
    if (vuRegs.length === 0) {
        throw new AsmError(`${mnemonic} requires VU register operands`, line);
    }
    for (const r of vuRegs) {
        if (r.code > 3) {
            throw new AsmError("Async VU operands must be pointer registers (VA-VM)", line);
        }
    }
    const dst = vuRegs[0].code;
    const src1 = vuRegs.length > 1 ? vuRegs[1].code : 0;
    let src2;
    if (mode === VU_MODE_VS) {
        const gprOps = operands.filter((op) => op.tag === TAG_REG);
        if (gprOps.length === 0) {
            throw new AsmError(`${mnemonic} broadcast requires a GPR operand (A-D)`, line);
        }
        if (gprOps[0].code > 3) {
            throw new AsmError("Broadcast GPR must be A-D", line);
        }
        src2 = gprOps[0].code;
    } else {
        src2 = vuRegs.length > 2 ? vuRegs[2].code : 0;
    }
    return encodeVuRegs(dst, src1, src2);
}

function _encodeVuAsync(mnemonic, suffixes, operands, line) {
    const opcode = _VU_MNEMONIC_TO_OP[mnemonic];
    if (opcode === undefined) {
        throw new AsmError(`Unknown VU async instruction: ${mnemonic}`, line);
    }

    const fmtSuffix = suffixes[0] || null;
    const modeSuffix = suffixes[1] || null;

    const fmt = _resolveVuFmt(mnemonic, fmtSuffix, line);
    const [mode, cond] = _resolveVuModeCond(mnemonic, modeSuffix, operands, line);

    // GPR broadcast restricted to byte formats
    if (mode === VU_MODE_VS && (VU_FMT_ELEM_SIZE[fmt] || 1) > 1) {
        throw new AsmError(`GPR broadcast only for byte formats (U/I/O3/O2), not .${fmtSuffix}`, line);
    }

    const regs = _encodeVuRegsFromOperands(operands, mnemonic, mode, line);
    const result = [opcode, encodeVfm(fmt, mode, cond), regs];

    if (mode === VU_MODE_VI) {
        const immOps = operands.filter((op) => op.tag === TAG_CONST);
        if (immOps.length === 0) {
            throw new AsmError(`${mnemonic} requires an immediate operand`, line);
        }
        const immVal = immOps[0].value;
        const elemSize = VU_FMT_ELEM_SIZE[fmt] || 1;
        for (let i = 0; i < elemSize; i++) {
            result.push((immVal >> (8 * i)) & 0xff);
        }
    }

    return result;
}

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
                // Binary file: embed raw bytes as a DB directive.
                const bytes = included instanceof ArrayBuffer ? new Uint8Array(included) : included;
                if (bytes.length > 256) {
                    const nParts = Math.ceil(bytes.length / 256);
                    throw new AsmError(
                        `@include "${path}": binary file is ${bytes.length} bytes — exceeds page size (256). ` +
                            `Split the file into ${nParts} parts (≤256 bytes each) and @include them on separate pages.`,
                        lineNo,
                        filename,
                    );
                }
                if (bytes.length > 0) {
                    const flatLineNo = outLines.length + 1;
                    lineMap.set(flatLineNo, { file: filename, line: lineNo });
                    outLines.push("DB " + Array.from(bytes).join(", "));
                }
            } else {
                _collectLines(included, files, path, new Set([...visited, path]), depth + 1, outLines, lineMap);
            }
        } else {
            const flatLineNo = outLines.length + 1;
            lineMap.set(flatLineNo, { file: filename, line: lineNo });
            outLines.push(text);
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

        for (let i = 0; i < operands.length; i++) {
            const op = operands[i];
            if (op.tag !== TAG_LABEL && op.tag !== TAG_ADDR_LABEL && op.tag !== TAG_PAGE_LABEL) continue;
            const isPageRef = op.tag === TAG_PAGE_LABEL;
            const isFpData = arch >= 2 && MNEMONICS_FP.has(pline.mnemonic) && !FP_CONTROL_MNEMONICS.has(pline.mnemonic);
            let patchPos;
            if (isFpData) {
                const fpCount = operands.filter((o) => o.tag === TAG_FP_REG).length;
                const nonFpIdx = operands.slice(0, i).filter((o) => o.tag !== TAG_FP_REG).length;
                patchPos = pos + 1 + fpCount + nonFpIdx;
            } else if (pline.mnemonic === "VSET") {
                // VSET encoding: [163, target, lo, hi]
                // {page} patches hi (pos+3), offset patches lo (pos+2)
                patchPos = isPageRef ? pos + 3 : pos + 2;
            } else {
                patchPos = pos + 1 + i;
            }
            labelPatches.push({
                page: st.currentPage,
                pos: patchPos,
                name: op.name,
                isPageRef,
                isJump,
                lineNo: pline.lineNo,
            });
        }

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

    // Labels: name → memory address
    const labels = {};
    for (const [name, info] of Object.entries(st.labelInfo)) {
        labels[name] = multi ? info.page * PAGE_SIZE + info.offset : info.offset;
    }

    // Mapping: flat code position → lineNo
    const mapping = {};
    for (const entry of st.pageMapping) {
        const flatPos = multi ? entry.page * PAGE_SIZE + entry.offset : entry.offset;
        mapping[flatPos] = entry.lineNo;
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
