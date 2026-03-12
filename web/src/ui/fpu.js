/**
 * FPU block renderer: FA/FB registers, rounding mode, status flags, format toggle.
 */

import { cpu, colors, hex } from "../state.js";
import { decodeFloat16Bits, decodeOfp8E4M3 } from "../../lib/fp.js";

// Sub-register names by physical register index, ordered MSB→LSB (display order)
const REG_NAMES = [
    { fp32: ["FA"], fp16: ["FHB", "FHA"], fp8: ["FQD", "FQC", "FQB", "FQA"] },
    { fp32: ["FB"], fp16: ["FHD", "FHC"], fp8: ["FQH", "FQG", "FQF", "FQE"] },
];

let fpuFmt = "hex";

const _fpBuf = new ArrayBuffer(4);
const _fpF32 = new Float32Array(_fpBuf);
const _fpU32 = new Uint32Array(_fpBuf);

function fpuRawBits(f) {
    _fpF32[0] = f;
    return _fpU32[0];
}

function renderFPUReg(bytesId, infoId, fVal, color, phys) {
    const raw = fpuRawBits(fVal);
    const bytes = [(raw >>> 24) & 0xff, (raw >>> 16) & 0xff, (raw >>> 8) & 0xff, raw & 0xff];
    const names = REG_NAMES[phys];

    let cells = "";
    let info = "";
    const bc = (lbl, val, span) =>
        `<div class="ri" style="flex:${span};">` +
        `<span class="ri-l" style="color:${color};font-size:7px;">${lbl}</span>` +
        `<span class="ri-v" style="color:${color};font-size:${val.length > 8 ? 9 : 11}px;">${val}</span></div>`;

    if (fpuFmt === "hex") {
        cells = bytes.map((b, i) => bc(`[${3 - i}]`, hex(b), 1)).join("");
        info = `= ${hex(raw, 8)}`;
    } else if (fpuFmt === "dec") {
        cells = bytes.map((b, i) => bc(`[${3 - i}]`, b.toString(), 1)).join("");
        info = `= ${raw}`;
    } else if (fpuFmt === "fp32") {
        cells = bc(names.fp32[0], fVal.toPrecision(6), 4);
        info = `${hex(raw, 8)}`;
    } else if (fpuFmt === "fp16") {
        const hi16 = (raw >>> 16) & 0xffff;
        const lo16 = raw & 0xffff;
        cells =
            bc(names.fp16[0], decodeFloat16Bits(hi16).toPrecision(4), 2) +
            bc(names.fp16[1], decodeFloat16Bits(lo16).toPrecision(4), 2);
        info = `${hex(hi16, 4)} ${hex(lo16, 4)}`;
    } else if (fpuFmt === "fp8") {
        cells = bytes.map((b, i) => bc(names.fp8[i], decodeOfp8E4M3(b).toPrecision(3), 1)).join("");
        info = bytes.map((b) => hex(b)).join(" ");
    }

    document.getElementById(bytesId).innerHTML = cells;
    document.getElementById(infoId).textContent = info;
}

export function renderFPU() {
    const fpu = cpu.fpu;
    if (!fpu) return;

    renderFPUReg("fpu-fa-bytes", "fpu-fa-info", fpu.fa, colors.gr, 0);
    renderFPUReg("fpu-fb-bytes", "fpu-fb-info", fpu.fb, colors.bl, 1);

    const rmNames = ["RNE", "RTZ", "RDN", "RUP"];
    const rmIdx = fpu.fpcr & 3;
    document.getElementById("fpu-rm").innerHTML = rmNames
        .map(
            (n, i) =>
                `<span class="fb ${i === rmIdx ? "fb-on" : "fb-off"}" style="font-size:8px;${i === rmIdx ? "border-color:" + colors.or + ";color:" + colors.or : ""}">${n}</span>`,
        )
        .join("");

    const fpsr = fpu.fpsr;
    const fl = [
        { n: "NV", b: 0 },
        { n: "DZ", b: 1 },
        { n: "OF", b: 2 },
        { n: "UF", b: 3 },
        { n: "NX", b: 4 },
    ];
    document.getElementById("fpu-flags").innerHTML = fl
        .map((f) => `<span class="fb ${(fpsr >> f.b) & 1 ? "fb-on" : "fb-off"}" style="font-size:8px;">${f.n}</span>`)
        .join("");
}

// Format toggle
document.getElementById("blk-fpu").addEventListener("click", (e) => {
    const t = e.target.closest("[data-ffmt]");
    if (!t) return;
    fpuFmt = t.dataset.ffmt;
    document.querySelectorAll("#fpu-fmt-tabs .ft").forEach((b) => b.classList.toggle("act", b.dataset.ffmt === fpuFmt));
    renderFPU();
});
