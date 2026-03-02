/**
 * Labels table renderer with click-to-navigate.
 */

import { cpu, asm, hex, printableChar } from '../state.js';
import { setPage } from './mem.js';

export function renderLabels() {
  const body = document.getElementById('labels-body');
  const entries = Object.entries(asm.labels).sort((a, b) => a[1] - b[1]);
  if (entries.length === 0) {
    body.innerHTML = '<tr><td colspan="4" class="py-1" style="color:var(--t-dim);">no labels</td></tr>';
    return;
  }
  body.innerHTML = entries.map(([name, addr]) => {
    const val = cpu.mem.get(addr);
    const ch = printableChar(val) ? `'${printableChar(val)}'` : '';
    return `<tr style="cursor:pointer;" data-addr="${addr}"><td class="py-1">${name}</td><td class="py-1" style="color:var(--a-orange);">${hex(addr, 4)}</td><td class="py-1">${hex(val)}</td><td class="py-1" style="color:var(--a-green);">${ch}</td></tr>`;
  }).join('');
}

// Click on label row navigates to its memory page
document.getElementById('labels-body').addEventListener('click', e => {
  const row = e.target.closest('[data-addr]');
  if (!row) return;
  const addr = parseInt(row.dataset.addr);
  setPage((addr >>> 8) & 0xFF);
});
