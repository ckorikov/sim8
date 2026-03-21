/**
 * CPU block renderer: registers, pointers, flags, state icon, format toggle.
 */

import { cpu, colors, regColors, hex, initFormatToggle } from "../state.js";

const cpuFmt = initFormatToggle("blk-cpu", "#cpu-fmt-tabs", "cfmt", () => renderCPU());

function cpuFmtVal(v) {
    return cpuFmt.get() === "dec" ? v.toString().padStart(3, " ") : hex(v);
}

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

export function renderCPU() {
    const ri = (n, v) =>
        `<div class="ri"><span class="ri-l" style="color:${regColors[n] || colors.dim}">${n}</span><span class="ri-v" style="color:${regColors[n] || colors.txt}">${cpuFmtVal(v)}</span></div>`;
    const fl = (n, v) =>
        `<span class="fb" style="border-color:${v ? colors.or : "var(--t-border)"};color:${v ? colors.or : colors.dim};min-width:var(--s-flag-min-w);">${n}</span>`;

    document.getElementById("cpu-regs").innerHTML = ri("A", cpu.a) + ri("B", cpu.b) + ri("C", cpu.c) + ri("D", cpu.d);
    document.getElementById("cpu-ptrs").innerHTML = ri("IP", cpu.ip) + ri("SP", cpu.sp) + ri("DP", cpu.dp);
    document.getElementById("cpu-flags").innerHTML = fl("Z", cpu.zero) + fl("C", cpu.carry) + fl("F", cpu.fault);

    document.getElementById("nav-cycles").textContent = `${cpu.cycles} cycles`;
    document.getElementById("nav-peak-mem").textContent = `${cpu.peakMem}B`;

    const sc = STATE_INFO[cpu.state] || STATE_INFO.IDLE;
    const si = document.getElementById("cpu-state-icon");
    si.innerHTML = sc.icon;
    si.style.color = colors[sc.colorKey];
    si.title = cpu.state;
}
