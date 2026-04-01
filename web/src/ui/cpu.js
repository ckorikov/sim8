/**
 * CPU block renderer: registers, pointers, flags, state icon, format toggle.
 */

import { cpu, colors, regColors, hex, initFormatToggle } from "../state.js";
import { isHidden, bindToggleClicks } from "./marker-toggle.js";

const cpuFmt = initFormatToggle("blk-cpu", "#cpu-fmt-tabs", "cfmt", () => renderCPU());

function cpuFmtVal(v) {
    return cpuFmt.get() === "dec" ? v.toString().padStart(3, " ") : hex(v);
}

// ── Cached DOM elements ──────────────────────────────────────────
const elRegs = document.getElementById("cpu-regs");
const elPtrs = document.getElementById("cpu-ptrs");
const elFlags = document.getElementById("cpu-flags");
const elCycles = document.getElementById("nav-cycles");
const elPeakMem = document.getElementById("nav-peak-mem");
const elStateIcon = document.getElementById("cpu-state-icon");

const STATE_INFO = {
    IDLE: {
        icon: '<svg width="8" height="8" viewBox="0 0 8 8"><circle cx="4" cy="4" r="3" fill="currentColor"/></svg>',
        colorKey: "mid",
    },
    RUNNING: {
        icon: '<svg width="8" height="8" viewBox="0 0 8 8"><polygon points="1.5,1 7,4 1.5,7" fill="currentColor"/></svg>',
        colorKey: "gr",
    },
    HALTED: {
        icon: '<svg width="8" height="8" viewBox="0 0 8 8"><rect x="1.5" y="1.5" width="5" height="5" rx="0.5" fill="currentColor"/></svg>',
        colorKey: "yl",
    },
    FAULT: {
        icon: '<svg width="8" height="8" viewBox="0 0 8 8"><line x1="1.5" y1="1.5" x2="6.5" y2="6.5" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/><line x1="6.5" y1="1.5" x2="1.5" y2="6.5" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/></svg>',
        colorKey: "rd",
    },
};

bindToggleClicks("blk-cpu");

export function renderCPU() {
    const ri = (n, v) => {
        const off = isHidden(n);
        const lc = off ? colors.dim : regColors[n] || colors.dim;
        const vc = off ? colors.txt : regColors[n] || colors.txt;
        return `<div class="ri"><span class="ri-l" style="color:${lc}">${n}</span><span class="ri-v" style="color:${vc}">${cpuFmtVal(v)}</span></div>`;
    };
    const fl = (n, v) =>
        `<span class="fb" style="border-color:${v ? colors.or : "var(--t-border)"};color:${v ? colors.or : colors.dim};min-width:var(--s-flag-min-w);">${n}</span>`;

    elRegs.innerHTML = ri("A", cpu.a) + ri("B", cpu.b) + ri("C", cpu.c) + ri("D", cpu.d);
    elPtrs.innerHTML = ri("IP", cpu.ip) + ri("SP", cpu.sp) + ri("DP", cpu.dp);
    elFlags.innerHTML = fl("Z", cpu.zero) + fl("C", cpu.carry) + fl("F", cpu.fault);

    elCycles.textContent = `${cpu.cycles} cycles`;
    elPeakMem.textContent = `${cpu.peakMem}B`;

    const sc = STATE_INFO[cpu.state] || STATE_INFO.IDLE;
    elStateIcon.innerHTML = sc.icon;
    elStateIcon.style.color = colors[sc.colorKey];
    elStateIcon.title = cpu.state;
}
