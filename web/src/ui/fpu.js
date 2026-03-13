/**
 * FPU block renderer: FA/FB registers, rounding mode, status flags, format toggle.
 */

import { cpu, colors, hex } from "../state.js";
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

let fpuFmt = "hex";

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
    } else if (fpuFmt === "F") {
        cells = bc(names.F[0], fVal.toPrecision(6), 4);
        info = `${hex(raw, 8)}`;
    } else if (fpuFmt in FMT_16) {
        const decode = FMT_16[fpuFmt];
        const hi16 = (raw >>> 16) & 0xffff;
        const lo16 = raw & 0xffff;
        cells =
            bc(names[fpuFmt][0], decode(hi16).toPrecision(4), 2) + bc(names[fpuFmt][1], decode(lo16).toPrecision(4), 2);
        info = `${hex(hi16, 4)} ${hex(lo16, 4)}`;
    } else if (fpuFmt in FMT_8) {
        const decode = FMT_8[fpuFmt];
        cells = bytes.map((b, i) => bc(names[fpuFmt][i], decode(b).toPrecision(3), 1)).join("");
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
