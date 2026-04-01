/**
 * FPU block renderer: FA/FB registers, rounding mode, status flags, format toggle.
 */

import { cpu, colors, hex, initFormatToggle, FPSR_FLAGS } from "../state.js";
import { decodeFloat16Bits, decodeBfloat16, decodeOfp8E4M3, decodeOfp8E5M2 } from "../../lib/fp.js";

// Sub-register names by physical register index, ordered MSB→LSB (display order)
const REG_NAMES = [
    {
        F: ["FA"],
        H: ["FHB", "FHA"],
        BF: ["FHB", "FHA"],
        O3: ["FQD", "FQC", "FQB", "FQA"],
        O2: ["FQD", "FQC", "FQB", "FQA"],
    },
    {
        F: ["FB"],
        H: ["FHD", "FHC"],
        BF: ["FHD", "FHC"],
        O3: ["FQH", "FQG", "FQF", "FQE"],
        O2: ["FQH", "FQG", "FQF", "FQE"],
    },
];

const RM_NAMES = ["RNE", "RTZ", "RDN", "RUP"];

const fpuFmt = initFormatToggle("blk-fpu", "#fpu-fmt-tabs", "ffmt", () => renderFPU());

const _fpBuf = new ArrayBuffer(4);
const _fpF32 = new Float32Array(_fpBuf);
const _fpU32 = new Uint32Array(_fpBuf);

function fpuRawBits(f) {
    _fpF32[0] = f;
    return _fpU32[0];
}

function decodeBf16Bits(bits) {
    return decodeBfloat16([bits & 0xff, (bits >> 8) & 0xff]);
}

const FMT_16 = { H: decodeFloat16Bits, BF: decodeBf16Bits };
const FMT_8 = { O3: decodeOfp8E4M3, O2: decodeOfp8E5M2 };

// Cached DOM elements
const elFaBytes = document.getElementById("fpu-fa-bytes");
const elFaInfo = document.getElementById("fpu-fa-info");
const elFbBytes = document.getElementById("fpu-fb-bytes");
const elFbInfo = document.getElementById("fpu-fb-info");
const elRm = document.getElementById("fpu-rm");
const elFpuFlags = document.getElementById("fpu-flags");

const _regEls = [
    [elFaBytes, elFaInfo],
    [elFbBytes, elFbInfo],
];

function renderFPUReg(phys, fVal, color) {
    const [elBytes, elInfo] = _regEls[phys];
    const raw = fpuRawBits(fVal);
    const bytes = [(raw >>> 24) & 0xff, (raw >>> 16) & 0xff, (raw >>> 8) & 0xff, raw & 0xff];
    const names = REG_NAMES[phys];

    let cells = "";
    let info = "";
    const bc = (lbl, val, span) =>
        `<div class="ri" style="flex:${span};">` +
        `<span class="ri-l" style="color:${color};font-size:7px;">${lbl}</span>` +
        `<span class="ri-v" style="color:${color};font-size:${val.length > 8 ? 9 : 11}px;">${val}</span></div>`;

    const fmt = fpuFmt.get();
    if (fmt === "hex") {
        cells = bytes.map((b, i) => bc(`[${3 - i}]`, hex(b), 1)).join("");
        info = `= ${hex(raw, 8)}`;
    } else if (fmt === "dec") {
        cells = bytes.map((b, i) => bc(`[${3 - i}]`, b.toString(), 1)).join("");
        info = `= ${raw}`;
    } else if (fmt === "F") {
        cells = bc(names.F[0], fVal.toPrecision(6), 4);
        info = `${hex(raw, 8)}`;
    } else if (fmt in FMT_16) {
        const decode = FMT_16[fmt];
        const hi16 = (raw >>> 16) & 0xffff;
        const lo16 = raw & 0xffff;
        cells = bc(names[fmt][0], decode(hi16).toPrecision(4), 2) + bc(names[fmt][1], decode(lo16).toPrecision(4), 2);
        info = `${hex(hi16, 4)} ${hex(lo16, 4)}`;
    } else if (fmt in FMT_8) {
        const decode = FMT_8[fmt];
        cells = bytes.map((b, i) => bc(names[fmt][i], decode(b).toPrecision(3), 1)).join("");
        info = bytes.map((b) => hex(b)).join(" ");
    }

    elBytes.innerHTML = cells;
    elInfo.textContent = info;
}

export function renderFPU() {
    const fpu = cpu.fpu;
    if (!fpu) return;

    renderFPUReg(0, fpu.fa, colors.gr);
    renderFPUReg(1, fpu.fb, colors.bl);

    const rmIdx = fpu.fpcr & 3;
    elRm.innerHTML = RM_NAMES.map(
        (n, i) =>
            `<span class="fb ${i === rmIdx ? "fb-on" : "fb-off"}" style="font-size:8px;${i === rmIdx ? "border-color:" + colors.or + ";color:" + colors.or : ""}">${n}</span>`,
    ).join("");

    const fpsr = fpu.fpsr;
    elFpuFlags.innerHTML = FPSR_FLAGS.map(
        (f) => `<span class="fb ${(fpsr >> f.bit) & 1 ? "fb-on" : "fb-off"}" style="font-size:8px;">${f.n}</span>`,
    ).join("");
}
