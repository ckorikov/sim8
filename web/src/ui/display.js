/**
 * Display block renderer: I/O character output (addresses 232-255).
 */

import { cpu, IO_BASE, printableChar } from '../state.js';

export function renderDisplay() {
  let ch = '';
  for (let i = IO_BASE; i <= 0xFF; i++) {
    const v = cpu.mem.get(i);
    const c = printableChar(v);
    ch += `<span class="cc ${c ? 'on' : ''}">${c || '&nbsp;'}</span>`;
  }
  document.getElementById('disp-chars').innerHTML =
    `<div style="display:inline-flex;gap:1px;">${ch}</div>`;
}
