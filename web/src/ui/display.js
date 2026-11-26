/**
 * Display block renderer: I/O character output (addresses 232-255).
 */

import { cpu, IO_BASE, printableChar, escapeHtml } from "../state.js";

const elDisp = document.getElementById("disp-chars");

export function renderDisplay() {
    let ch = "";
    for (let i = IO_BASE; i <= 0xff; i++) {
        const v = cpu.mem.get(i);
        const c = printableChar(v);
        ch += `<span class="cc ${c ? "on" : ""}">${c ? escapeHtml(c) : "&nbsp;"}</span>`;
    }
    elDisp.innerHTML = `<div style="display:inline-flex;gap:1px;">${ch}</div>`;
}
