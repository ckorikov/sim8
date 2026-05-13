/**
 * Vector Unit block renderer: registers, queue, status dot, format toggle.
 */

import { colors, hex, initFormatToggle, fpsrFlagsHtml } from "../state.js";
import { VU_QUEUE_DEPTH } from "../../lib/vu.js";
import { isHidden, bindToggleClicks } from "./marker-toggle.js";

let _lastVu = null;
const vuFmt = initFormatToggle("blk-vu", "#vu-fmt-tabs", "vfmt", () => renderVU(_lastVu));

const elPtrs = document.getElementById("vu-ptrs");
const elML = document.getElementById("vu-ml");
const elFlags = document.getElementById("vu-flags");
const elQueue = document.getElementById("vu-queue");
const elQueueDepth = document.getElementById("vu-queue-depth");
const elDot = document.getElementById("vu-state-dot");

const DOT_COLORS = { IDLE: "dim", BUSY: "gr" };

bindToggleClicks("blk-vu");

function renderQueueSlot(item) {
    if (!item) return `<div class="vu-queue-slot">&mdash;</div>`;
    const cls = item.active ? "vu-queue-slot active" : "vu-queue-slot pending";
    return `<div class="${cls}"><span class="vu-q-mn">${item.label}</span> <span class="vu-q-op">${item.operands}</span></div>`;
}

function ri(name, value, color, pad) {
    const formatted = vuFmt.get() === "dec" ? value.toString() : hex(value, pad);
    const off = isHidden(name);
    const lc = off ? colors.dim : color;
    const vc = off ? colors.txt : color;
    return (
        `<div class="ri">` +
        `<span class="ri-l" style="color:${lc}">${name}</span>` +
        `<span class="ri-v" style="color:${vc}">${formatted}</span>` +
        `</div>`
    );
}

const EMPTY_REGS = { va: 0, vb: 0, vc: 0, vm: 0, vl: 0, vfpsr: 0 };

/** @param {import('../../lib/vu.js').VectorUnit | null} vu */
export function renderVU(vu) {
    _lastVu = vu;
    const { va, vb, vc, vm, vl, vfpsr } = vu ? vu.regs : EMPTY_REGS;
    const vuState = vu ? vu.state : "IDLE";
    const queueItems = vu ? vu.queueItems : [];

    elPtrs.innerHTML = ri("VA", va, colors.gr, 4) + ri("VB", vb, colors.bl, 4) + ri("VC", vc, colors.or, 4);
    elML.innerHTML = ri("VM", vm, colors.rd, 4) + ri("VL", vl, colors.mid, 4);

    elFlags.innerHTML = fpsrFlagsHtml(vfpsr, colors.or);

    elQueueDepth.textContent = `${queueItems.length}/${VU_QUEUE_DEPTH}`;

    elQueue.innerHTML = Array.from({ length: VU_QUEUE_DEPTH }, (_, i) => renderQueueSlot(queueItems[i])).join("");

    elDot.style.background = colors[DOT_COLORS[vuState] || "dim"];
    elDot.classList.toggle("vu-busy", vuState === "BUSY");
}
