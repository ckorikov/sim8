/**
 * Display block renderer: I/O character output (addresses 232-251, 20 chars).
 */

import { cpu, IO_BASE, IO_DISPLAY_END, printableChar, escapeHtml } from "../state.js";

const elDisp = document.getElementById("disp-chars");

export function renderDisplay() {
    const chars = Array.from({ length: IO_DISPLAY_END - IO_BASE }, (_, i) => {
        const c = printableChar(cpu.mem.get(IO_BASE + i));
        return `<span class="cc ${c ? "on" : ""}">${c ? escapeHtml(c) : "&nbsp;"}</span>`;
    }).join("");
    elDisp.innerHTML = chars;
}
