/**
 * Memory block renderer: 16x16 grid, page navigation, format toggle, instruction highlighting.
 */

import { cpu, colors, asm, hex, printableChar, cssVar, STACK_BASE, IO_BASE, PAGE_SIZE } from '../state.js';

let memFmt = 'hex';
let page = 0;

function fmtByte(v) {
  return memFmt === 'dec' ? v.toString().padStart(3, ' ') : hex(v);
}

function cellClass(addr, val, showInstr) {
  const pageBase = page * PAGE_SIZE;
  const absAddr = pageBase + addr;
  let cl = 'mem-cell';

  if (absAddr === cpu.ip) return cl + ' marker-ip';
  if (absAddr === cpu.sp) return cl + ' marker-sp';

  if (page === 0) {
    if (showInstr && asm.instrStarts.has(addr)) cl += ' instr-start';
    else if (showInstr && addr < asm.codeLen && val) cl += ' instr';
    else if (addr >= STACK_BASE && addr < IO_BASE) cl += ' stack';
    else if (addr >= IO_BASE) cl += ' io';
  }

  if (absAddr === cpu.a && absAddr !== cpu.ip) cl += ' marker-a';
  if (absAddr === cpu.b && absAddr !== cpu.ip) cl += ' marker-b';
  if (absAddr === cpu.c && absAddr !== cpu.ip) cl += ' marker-c';
  if (absAddr === cpu.d && absAddr !== cpu.ip) cl += ' marker-d';
  return cl;
}

export function renderMemory() {
  const showInstr = document.getElementById('chk-instr').checked;
  const baseCw = parseInt(cssVar('--s-mem-cell-w')) || 28;
  const cellW = memFmt === 'dec' ? baseCw + 2 : baseCw;
  const rowW = parseInt(cssVar('--s-mem-row-w')) || 24;
  const cellFont = parseInt(cssVar('--s-mem-cell-font')) || 10;
  const pageBase = page * PAGE_SIZE;

  const rows = [];
  const hdrs = Array.from({ length: 16 }, (_, c) => `<div class="mh" style="width:${cellW}px">${hex(c, 1)}</div>`).join('');
  rows.push(`<div style="display:flex;"><div class="mr" style="width:${rowW}px"></div>${hdrs}</div>`);

  for (let r = 0; r < 16; r++) {
    const cells = Array.from({ length: 16 }, (_, c) => {
      const addr = r * 16 + c;
      const absAddr = pageBase + addr;
      const val = cpu.mem.get(absAddr);
      const ch = printableChar(val);
      return `<div class="${cellClass(addr, val, showInstr)}" style="width:${cellW}px;font-size:${cellFont}px" title="[${hex(absAddr, 4)}]=${hex(val)} ${ch}">${fmtByte(val)}</div>`;
    }).join('');
    rows.push(`<div style="display:flex;"><div class="mr" style="width:${rowW}px">${hex(pageBase + r * 16, 4)}</div>${cells}</div>`);
  }

  const legend = [
    [colors.mid, 'data'], [colors.yl, 'stack'], [colors.gr, 'i/o'], [colors.or, 'ip'], [colors.yl, 'sp']
  ].map(([c, l]) => `<span><b style="color:${c};">&#9632;</b> ${l}</span>`).join('');

  document.getElementById('mem-grid').innerHTML =
    `<div style="line-height:0;display:inline-block;">${rows.join('')}</div>` +
    `<div style="margin-top:8px;display:flex;gap:12px;font-size:8px;color:${colors.dim};justify-content:center;">${legend}</div>`;
}

export function setPage(p) {
  page = p;
  updatePageLabel();
  renderMemory();
}

function updatePageLabel() {
  document.getElementById('page-num').textContent = `${page}/255`;
}

// Instructions checkbox
document.getElementById('chk-instr').addEventListener('change', () => renderMemory());

// Format toggle
document.getElementById('blk-mem').addEventListener('click', e => {
  const t = e.target.closest('[data-fmt]');
  if (!t) return;
  memFmt = t.dataset.fmt;
  document.querySelectorAll('#fmt-tabs .ft').forEach(b => b.classList.toggle('act', b.dataset.fmt === memFmt));
  renderMemory();
});

// Page navigation
document.getElementById('page-prev').addEventListener('click', () => {
  if (page > 0) { page--; updatePageLabel(); renderMemory(); }
});
document.getElementById('page-next').addEventListener('click', () => {
  if (page < 255) { page++; updatePageLabel(); renderMemory(); }
});
