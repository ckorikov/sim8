/**
 * sim8 v2 — Browser UI entry point.
 * Wires real CPU (core.js) and assembler (asm.js) into the design shell.
 */

import { assemble, AsmError } from './asm.js';
import { CPU, CpuState, ErrorCode, IO_START, PAGE_SIZE, SP_INIT } from './core.js';
import { Op, BY_CODE_FP, MNEMONICS, MNEMONICS_FP, REGISTERS, FP_REGISTERS } from './isa.js';
import { decodeFloat16Bits, decodeOfp8E4M3 } from './fp.js';

// ── Constants ──────────────────────────────────────────────────

const STACK_BASE = SP_INIT - 2;
const IO_BASE    = IO_START;  // 232
const WIRE_FLASH_MS = 350;

// CodeMirror syntax patterns (generated from isa.js exports)
const ALL_MNEMONICS_RE = new RegExp(
  '\\b(' + [...MNEMONICS, ...MNEMONICS_FP].join('|') + ')\\b', 'i'
);
const ALL_REGISTERS_RE = new RegExp(
  '\\b(' + [...Object.keys(REGISTERS), ...Object.keys(FP_REGISTERS)].join('|') + ')\\b'
);
const WIRE_DATA = 0, WIRE_FP = 1, WIRE_IO = 2;

// ── CPU instance ───────────────────────────────────────────────

let cpu = new CPU();

// ── Assembly state ─────────────────────────────────────────────

let asmLabels = {};     // label name → address
let asmMapping = {};    // address → source line (1-based)
let instrStarts = new Set();
let codeLen = 0;

// ── Editor refs (set after CodeMirror init) ────────────────────

let cmView = null;
let cmExecEffect = null;
let cmScrollIntoView = null;

// ── Default example code ───────────────────────────────────────

const defaultCode = `; Simple example
; Writes Hello World to the output

        JMP start
hello:
        DB "Hello World!"    ; Variable
        DB 0                 ; String terminator

start:
        MOV C, hello         ; Point to var
        MOV D, 232           ; Point to output
        CALL print
        HLT                  ; Stop execution

print:                       ; print(C:*from, D:*to)
        PUSH A
        PUSH B
        MOV B, 0

.loop:
        MOV A, [C]           ; Get char from var
        MOV [D], A           ; Write to output
        INC C
        INC D
        CMP B, [C]           ; Check if end
        JNZ .loop            ; jump if not

        POP B
        POP A
        RET

`;

// ── Assemble helper ────────────────────────────────────────────

function doAssemble(source) {
  const errEl = document.getElementById('asm-error');
  errEl.classList.add('hidden');
  errEl.textContent = '';

  try {
    const result = assemble(source);
    codeLen = result.code.length;
    asmLabels = result.labels;
    asmMapping = result.mapping;

    // Build instruction starts set
    instrStarts = new Set(Object.keys(asmMapping).map(Number));

    // Load into CPU
    cpu.reset();
    cpu.load(result.code);

    // Render labels table
    renderLabels();
    renderAll();
    return true;
  } catch (e) {
    errEl.textContent = e instanceof AsmError ? e.message : 'Internal error: ' + e.message;
    errEl.classList.remove('hidden');
    return false;
  }
}

// ── Execution highlight ────────────────────────────────────────

function highlightExecLine(line) {
  if (!cmView || !cmExecEffect) return;
  cmView.dispatch({ effects: cmExecEffect.of(line) });
  if (cmScrollIntoView && line >= 1 && line <= cmView.state.doc.lines) {
    const pos = cmView.state.doc.line(line).from;
    cmView.dispatch({ effects: cmScrollIntoView(pos, { y: 'center' }) });
  }
}

// ── Wire flash ─────────────────────────────────────────────────

function flashWire(idx) {
  const edge = document.querySelectorAll('#wire-canvas .x6-edge')[idx];
  if (!edge) return;
  edge.classList.add('wire-active');
  setTimeout(() => edge.classList.remove('wire-active'), WIRE_FLASH_MS);
}

// ── Render helpers ─────────────────────────────────────────────

function renderAll() {
  renderCPU(); renderFPU(); renderMemory(); renderDisplay();
  const line = asmMapping[cpu.ip];
  highlightExecLine(line !== undefined ? line : -1);
}

// ── Colors (read from CSS vars for theme switching) ────────────

function cssVar(name) { return getComputedStyle(document.documentElement).getPropertyValue(name).trim(); }
function getColors() {
  return { or:cssVar('--a-orange'), bl:cssVar('--a-blue'), gr:cssVar('--a-green'), rd:cssVar('--a-red'), yl:cssVar('--a-yellow'),
           dim:cssVar('--t-dim'), mid:cssVar('--t-mid'), txt:cssVar('--t-text') };
}
let colors = getColors();
function getRegColors() { return { A:colors.gr, B:colors.bl, C:colors.or, D:colors.rd, IP:colors.or, SP:colors.yl, DP:colors.mid }; }
let regColors = getRegColors();

function hex(v, p = 2) { return v.toString(16).toUpperCase().padStart(p, '0'); }
function printableChar(v) { return (v >= 32 && v < 127) ? String.fromCharCode(v) : ''; }

// ── CPU view ───────────────────────────────────────────────────

let cpuFmt = 'hex';
function cpuFmtVal(v) { return cpuFmt === 'dec' ? v.toString().padStart(3, ' ') : hex(v); }

function cpuStateInfo(key) {
  const k = key.toLowerCase();
  const map = {
    idle:    { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><circle cx="4" cy="4" r="3" fill="currentColor"/></svg>`, color: colors.mid, title: 'IDLE' },
    running: { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><polygon points="1.5,1 7,4 1.5,7" fill="currentColor"/></svg>`, color: colors.gr, title: 'RUNNING' },
    halted:  { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><rect x="1.5" y="1.5" width="5" height="5" rx="0.5" fill="currentColor"/></svg>`, color: colors.yl, title: 'HALTED' },
    fault:   { icon: `<svg width="8" height="8" viewBox="0 0 8 8"><line x1="1.5" y1="1.5" x2="6.5" y2="6.5" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/><line x1="6.5" y1="1.5" x2="1.5" y2="6.5" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/></svg>`, color: colors.rd, title: 'FAULT' },
  };
  return map[k] || map.idle;
}

function renderCPU() {
  const ri = (n, v) => `<div class="ri"><span class="ri-l" style="color:${regColors[n]||colors.dim}">${n}</span><span class="ri-v" style="color:${regColors[n]||colors.txt}">${cpuFmtVal(v)}</span></div>`;
  const fl = (n, v) => `<span class="fb" style="border-color:${v?colors.or:'var(--t-border)'};color:${v?colors.or:colors.dim};min-width:var(--s-flag-min-w);">${n}</span>`;

  document.getElementById('cpu-regs').innerHTML = ri('A', cpu.a) + ri('B', cpu.b) + ri('C', cpu.c) + ri('D', cpu.d);
  document.getElementById('cpu-ptrs').innerHTML = ri('IP', cpu.ip) + ri('SP', cpu.sp) + ri('DP', cpu.dp);
  document.getElementById('cpu-flags').innerHTML = fl('Z', cpu.zero) + fl('C', cpu.carry) + fl('F', cpu.fault);

  document.getElementById('nav-cycles').textContent = `${cpu.cycles} cycles`;

  const sc = cpuStateInfo(cpu.state);
  const si = document.getElementById('cpu-state-icon');
  si.innerHTML = sc.icon;
  si.style.color = sc.color;
  si.title = sc.title;
}

// CPU format toggle
document.getElementById('blk-cpu').addEventListener('click', e => {
  const t = e.target.closest('[data-cfmt]');
  if (!t) return;
  cpuFmt = t.dataset.cfmt;
  document.querySelectorAll('#cpu-fmt-tabs .ft').forEach(b => b.classList.toggle('act', b.dataset.cfmt === cpuFmt));
  renderCPU();
});

// ── FPU view ───────────────────────────────────────────────────

let fpuFmt = 'hex';

const _fpBuf = new ArrayBuffer(4);
const _fpF32 = new Float32Array(_fpBuf);
const _fpU32 = new Uint32Array(_fpBuf);

function fpuRawBits(f) {
  _fpF32[0] = f;
  return _fpU32[0];
}

function renderFPUReg(bytesId, infoId, fVal, color) {
  const raw = fpuRawBits(fVal);
  const bytes = [(raw >>> 24) & 0xFF, (raw >>> 16) & 0xFF, (raw >>> 8) & 0xFF, raw & 0xFF];

  let cells = '';
  let info = '';
  const bc = (lbl, val, span) =>
    `<div class="ri" style="flex:${span};">` +
    `<span class="ri-l" style="color:${color};font-size:7px;">${lbl}</span>` +
    `<span class="ri-v" style="color:${color};font-size:${val.length > 8 ? 9 : 11}px;">${val}</span></div>`;

  if (fpuFmt === 'hex') {
    cells = bytes.map((b, i) => bc(`[${3 - i}]`, hex(b), 1)).join('');
    info = `= ${hex(raw, 8)}`;
  } else if (fpuFmt === 'dec') {
    cells = bytes.map((b, i) => bc(`[${3 - i}]`, b.toString(), 1)).join('');
    info = `= ${raw}`;
  } else if (fpuFmt === 'fp32') {
    cells = bc('f32', fVal.toPrecision(6), 4);
    info = `${hex(raw, 8)}`;
  } else if (fpuFmt === 'fp16') {
    const hi16 = (raw >>> 16) & 0xFFFF;
    const lo16 = raw & 0xFFFF;
    cells = bc('hi', decodeFloat16Bits(hi16).toPrecision(4), 2) + bc('lo', decodeFloat16Bits(lo16).toPrecision(4), 2);
    info = `${hex(hi16, 4)} ${hex(lo16, 4)}`;
  } else if (fpuFmt === 'fp8') {
    cells = bytes.map((b, i) => bc(`[${3 - i}]`, decodeOfp8E4M3(b).toPrecision(3), 1)).join('');
    info = bytes.map(b => hex(b)).join(' ');
  }

  document.getElementById(bytesId).innerHTML = cells;
  document.getElementById(infoId).textContent = info;
}

function renderFPU() {
  const fpu = cpu.fpu;
  if (!fpu) return;

  renderFPUReg('fpu-fa-bytes', 'fpu-fa-info', fpu.fa, colors.gr);
  renderFPUReg('fpu-fb-bytes', 'fpu-fb-info', fpu.fb, colors.bl);

  const rmNames = ['RNE', 'RTZ', 'RDN', 'RUP'];
  const rmIdx = fpu.fpcr & 3;
  document.getElementById('fpu-rm').innerHTML =
    rmNames.map((n, i) => `<span class="fb ${i === rmIdx ? 'fb-on' : 'fb-off'}" style="font-size:8px;${i === rmIdx ? 'border-color:' + colors.or + ';color:' + colors.or : ''}">${n}</span>`).join('');

  const fpsr = fpu.fpsr;
  const fl = [{ n: 'NV', b: 0 }, { n: 'DZ', b: 1 }, { n: 'OF', b: 2 }, { n: 'UF', b: 3 }, { n: 'NX', b: 4 }];
  document.getElementById('fpu-flags').innerHTML =
    fl.map(f => `<span class="fb ${(fpsr >> f.b) & 1 ? 'fb-on' : 'fb-off'}" style="font-size:8px;">${f.n}</span>`).join('');
}

// FPU format toggle
document.getElementById('blk-fpu').addEventListener('click', e => {
  const t = e.target.closest('[data-ffmt]');
  if (!t) return;
  fpuFmt = t.dataset.ffmt;
  document.querySelectorAll('#fpu-fmt-tabs .ft').forEach(b => b.classList.toggle('act', b.dataset.ffmt === fpuFmt));
  renderFPU();
});

// ── Memory view ────────────────────────────────────────────────

let memFmt = 'hex';
let page= 0;

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
    if (showInstr && instrStarts.has(addr)) cl += ' instr-start';
    else if (showInstr && addr < codeLen && val) cl += ' instr';
    else if (addr >= STACK_BASE && addr < IO_BASE) cl += ' stack';
    else if (addr >= IO_BASE) cl += ' io';
  }

  if (absAddr === cpu.a && absAddr !== cpu.ip) cl += ' marker-a';
  if (absAddr === cpu.b && absAddr !== cpu.ip) cl += ' marker-b';
  if (absAddr === cpu.c && absAddr !== cpu.ip) cl += ' marker-c';
  if (absAddr === cpu.d && absAddr !== cpu.ip) cl += ' marker-d';
  return cl;
}

function renderMemory() {
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
function updatePageLabel() { document.getElementById('page-num').textContent = `${page}/255`; }
document.getElementById('page-prev').addEventListener('click', () => {
  if (page > 0) { page--; updatePageLabel(); renderMemory(); }
});
document.getElementById('page-next').addEventListener('click', () => {
  if (page < 255) { page++; updatePageLabel(); renderMemory(); }
});

// ── Display ────────────────────────────────────────────────────

function renderDisplay() {
  let ch = '';
  for (let i = IO_BASE; i <= 0xFF; i++) {
    const v = cpu.mem.get(i);
    const c = printableChar(v);
    ch += `<span class="cc ${c ? 'on' : ''}">${c || '&nbsp;'}</span>`;
  }
  document.getElementById('disp-chars').innerHTML =
    `<div style="display:inline-flex;gap:1px;">${ch}</div>`;
}

// ── Labels table ───────────────────────────────────────────────

function renderLabels() {
  const body = document.getElementById('labels-body');
  const entries = Object.entries(asmLabels).sort((a, b) => a[1] - b[1]);
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
  page = (addr >>> 8) & 0xFF;
  updatePageLabel();
  renderMemory();
});

// ── CPU step (with wire flash) ─────────────────────────────────

function stepCPU() {
  if (cpu.state === CpuState.FAULT || cpu.state === CpuState.HALTED) return false;

  const prevIp = cpu.ip;
  const opcode = cpu.mem.get(prevIp);
  const wasRunning = cpu.step();

  // Flash wires based on opcode
  if (BY_CODE_FP[opcode] !== undefined) {
    flashWire(WIRE_FP);
  } else {
    flashWire(WIRE_DATA);
  }
  // Display continuously reads I/O memory — bus always active
  flashWire(WIRE_IO);

  renderAll();
  return wasRunning;
}

function resetCPU() {
  if (runTimer) stopRun();
  cpu.reset();
  // Re-load the current program if we have one
  if (codeLen > 0 && cmView) {
    const source = cmView.state.doc.toString();
    try {
      const result = assemble(source);
      cpu.load(result.code);
    } catch (e) {
      console.warn('Re-assembly on reset failed:', e.message);
    }
  }
  highlightExecLine(-1);
  renderAll();
}

// ── Run/Stop controls ──────────────────────────────────────────

const btnRun = document.getElementById('btn-run');
const btnStep = document.getElementById('btn-step');
const btnReset = document.getElementById('btn-reset');
const speedSel = document.getElementById('speed-select');
let runTimer = null;

function updateRunBtnColor() {
  btnRun.style.color = btnRun.dataset.state === 'run' ? cssVar('--a-green') : cssVar('--a-red');
}

function getSpeedMs() {
  const hz = parseInt(speedSel.value) || 4;
  return Math.round(1000 / hz);
}

function setRunUI(running) {
  btnRun.dataset.state = running ? 'stop' : 'run';
  btnRun.querySelector('svg').innerHTML = running
    ? '<rect x="3" y="3" width="10" height="10"/>'
    : '<polygon points="3,1 13,8 3,15"/>';
  btnRun.querySelector('span').textContent = running ? 'stop' : 'run';
  updateRunBtnColor();
}

function startRun() {
  if (runTimer) return;
  if (cpu.state === CpuState.HALTED || cpu.state === CpuState.FAULT) {
    resetCPU();
  }
  setRunUI(true);
  runTimer = setInterval(() => {
    if (!stepCPU()) stopRun();
  }, getSpeedMs());
}

function stopRun() {
  if (runTimer) { clearInterval(runTimer); runTimer = null; }
  if (cpu.state === CpuState.RUNNING) {
    cpu.state = CpuState.IDLE;
  }
  setRunUI(false);
  renderCPU();
}

btnRun.addEventListener('click', () => {
  if (runTimer) stopRun(); else startRun();
});

btnStep.addEventListener('click', () => {
  if (runTimer) stopRun();
  if (cpu.state === CpuState.HALTED || cpu.state === CpuState.FAULT) return;
  stepCPU();
  if (cpu.state === CpuState.RUNNING) {
    cpu.state = CpuState.IDLE;
    renderCPU();
  }
});

btnReset.addEventListener('click', () => resetCPU());

speedSel.addEventListener('change', () => {
  if (runTimer) { stopRun(); startRun(); }
});

// ── Assemble button ────────────────────────────────────────────

document.getElementById('btn-assemble').addEventListener('click', () => {
  if (runTimer) stopRun();
  const source = cmView
    ? cmView.state.doc.toString()
    : document.querySelector('#editor-container textarea')?.value || '';
  doAssemble(source);
});

// ── Wire theme sync ────────────────────────────────────────────

function updateWireColors() {
  const canvasBg = cssVar('--t-canvas');
  document.querySelectorAll('#wire-canvas rect[rx]').forEach(r => r.setAttribute('fill', canvasBg));
  const colors = [cssVar('--a-yellow'), cssVar('--a-orange'), cssVar('--a-green')];
  document.querySelectorAll('#wire-canvas .x6-edge').forEach((edge, i) => {
    const c = colors[i];
    if (!c) return;
    const line = edge.querySelector('path[stroke-dasharray]');
    if (line) line.setAttribute('stroke', c);
    edge.querySelectorAll('marker path, marker polygon').forEach(m => {
      m.setAttribute('fill', c); m.setAttribute('stroke', c);
    });
    const txt = edge.querySelector('text');
    if (txt) txt.setAttribute('fill', c);
  });
}

// ── Theme toggle ───────────────────────────────────────────────

let isDark = true;
document.getElementById('btn-theme').addEventListener('click', () => {
  isDark = !isDark;
  document.documentElement.classList.toggle('light', !isDark);
  document.getElementById('theme-icon-dark').classList.toggle('hidden', isDark);
  document.getElementById('theme-icon-light').classList.toggle('hidden', !isDark);
  document.getElementById('theme-label').textContent = isDark ? 'light' : 'dark';

  colors = getColors();
  regColors = getRegColors();
  renderAll();
  updateRunBtnColor();
  updateWireColors();
});

// ── Initial render ─────────────────────────────────────────────

renderAll();

// ── Layout adjustment ──────────────────────────────────────────

requestAnimationFrame(() => {
  const cpuEl = document.getElementById('blk-cpu');
  const fpuEl = document.getElementById('blk-fpu');
  const memEl = document.getElementById('blk-mem');
  const dispEl = document.getElementById('blk-disp');
  const wireGap = parseInt(cssVar('--s-wire-gap')) || 56;

  const cpuH = cpuEl.offsetHeight;
  const fpuH = fpuEl.offsetHeight;
  const maxH = Math.max(cpuH, fpuH);
  const topY = parseInt(cssVar('--s-top-y')) || 32;
  if (cpuH < fpuH) cpuEl.style.top = (topY + Math.round((fpuH - cpuH) / 2)) + 'px';
  if (fpuH < cpuH) fpuEl.style.top = (topY + Math.round((cpuH - fpuH) / 2)) + 'px';

  const topBottom = topY + maxH;
  memEl.style.top = (topBottom + wireGap) + 'px';

  const memTop = parseInt(memEl.style.top);
  const memH = memEl.offsetHeight;
  dispEl.style.top = (memTop + memH + wireGap) + 'px';

  const container = document.getElementById('diagram-container');
  const dispTop = parseInt(dispEl.style.top);
  container.style.height = (dispTop + dispEl.offsetHeight + 32) + 'px';

  initWires();
});

// ── X6 Wires ───────────────────────────────────────────────────

function initWires() {
  if (typeof X6 === 'undefined') {
    document.getElementById('wire-canvas').innerHTML =
      '<div style="position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);color:#cc4444;">X6 failed to load</div>';
    return;
  }

  const container = document.getElementById('diagram-container');
  const cRect = container.getBoundingClientRect();
  const canvas = document.getElementById('wire-canvas');
  const cW = container.offsetWidth;
  const cH = container.offsetHeight;
  canvas.style.width = cW + 'px';
  canvas.style.height = cH + 'px';

  const { Graph } = X6;
  const graph = new Graph({
    container: canvas,
    width: cW,
    height: cH,
    background: false,
    grid: false,
    interacting: false,
  });

  function portPos(portId) {
    const port = document.getElementById(portId);
    const pr = port.getBoundingClientRect();
    return {
      x: Math.round(pr.left - cRect.left + pr.width / 2),
      y: Math.round(pr.top - cRect.top + pr.height / 2),
    };
  }

  function addWire(fromId, toId, color, label, opts = {}) {
    const from = portPos(fromId);
    const to = portPos(toId);
    const bidir = opts.bidir !== false;
    const labelOffset = opts.labelOffset || 0;
    const lineAttrs = {
      stroke: color, strokeWidth: 1.5, strokeDasharray: '6 3',
      targetMarker: { name: 'block', width: 6, height: 4, fill: color, stroke: color },
    };
    if (bidir) {
      lineAttrs.sourceMarker = { name: 'block', width: 6, height: 4, fill: color, stroke: color };
    }

    let verts = opts.vertices || [];
    if (!opts.vertices) {
      const dx = Math.abs(to.x - from.x);
      const dy = Math.abs(to.y - from.y);
      if (dx < 4) {
        // Vertical
      } else if (dy < 4) {
        // Horizontal
      } else {
        const midY = Math.round((from.y + to.y) / 2);
        verts = [{ x: from.x, y: midY }, { x: to.x, y: midY }];
      }
    }

    graph.addEdge({
      source: { x: from.x, y: from.y },
      target: { x: to.x, y: to.y },
      vertices: verts,
      router: { name: 'normal' },
      connector: { name: 'rounded', args: { radius: 8 } },
      attrs: { line: lineAttrs },
      labels: [{ position: { distance: 0.5, offset: labelOffset }, attrs: {
        text: { text: label, fontSize: 9, fontFamily: "'JetBrains Mono',monospace", fill: color, letterSpacing: '0.05em' },
        rect: { fill: cssVar('--t-canvas'), rx: 2, ry: 2 },
      } }],
    });
  }

  addWire('port-cpu-bottom', 'port-mem-top', colors.yl, 'data bus');
  addWire('port-cpu-right', 'port-fpu-left', colors.or, 'fp bus', { labelOffset: -12 });
  addWire('port-mem-bottom', 'port-disp-top', colors.gr, 'i/o', { bidir: false, labelOffset: 20 });
}

// ── Responsive diagram scaling ─────────────────────────────────

function fitDiagram() {
  const section = document.getElementById('diagram-section');
  const container = document.getElementById('diagram-container');
  const natW = parseInt(cssVar('--s-diagram-w')) || 840;
  const availW = section.clientWidth - 32;
  const scale = Math.min(availW / natW, 1);
  container.style.transform = `scale(${scale})`;
  const natH = parseInt(container.style.height) || container.offsetHeight;
  container.style.marginBottom = (-(1 - scale) * natH) + 'px';
}

// ── Split handle drag ──────────────────────────────────────────

(() => {
  const handle = document.getElementById('split-handle');
  const left = document.getElementById('left-panel');
  let dragging = false;

  handle.addEventListener('mousedown', e => {
    e.preventDefault();
    dragging = true;
    handle.classList.add('active');
    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';
  });

  window.addEventListener('mousemove', e => {
    if (!dragging) return;
    const mainRect = left.parentElement.getBoundingClientRect();
    const x = e.clientX - mainRect.left;
    const pct = Math.min(Math.max(x / mainRect.width * 100, 15), 70);
    left.style.width = pct + '%';
    fitDiagram();
  });

  window.addEventListener('mouseup', () => {
    if (!dragging) return;
    dragging = false;
    handle.classList.remove('active');
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
  });

  window.addEventListener('resize', fitDiagram);
  requestAnimationFrame(fitDiagram);
})();

// ── CodeMirror initialization ──────────────────────────────────

(async () => {
  const ct = document.getElementById('editor-container');
  try {
    const { EditorView, basicSetup } = await import('https://esm.sh/codemirror');
    const { EditorState, StateEffect, StateField } = await import('https://esm.sh/@codemirror/state');
    const { Decoration, GutterMarker, gutter } = await import('https://esm.sh/@codemirror/view');
    const { StreamLanguage, HighlightStyle, syntaxHighlighting } = await import('https://esm.sh/@codemirror/language');
    const { tags } = await import('https://esm.sh/@lezer/highlight');

    const setExecLine = StateEffect.define();
    cmExecEffect = setExecLine;
    const execLineDeco = Decoration.line({ class: 'cm-exec-line' });

    class ExecMarker extends GutterMarker {
      toDOM() {
        const el = document.createElement('span');
        el.textContent = '\u25B6';
        el.className = 'cm-exec-arrow';
        return el;
      }
    }
    const execMarker = new ExecMarker();

    const execLineField = StateField.define({
      create() { return { line: -1, decos: Decoration.none }; },
      update(state, tr) {
        for (const e of tr.effects) {
          if (e.is(setExecLine)) {
            if (e.value < 1) return { line: -1, decos: Decoration.none };
            const doc = tr.state.doc;
            if (e.value > doc.lines) return { line: -1, decos: Decoration.none };
            const lineStart = doc.line(e.value).from;
            return {
              line: e.value,
              decos: Decoration.set([execLineDeco.range(lineStart)]),
            };
          }
        }
        return state;
      },
    });
    const execDecoExt = EditorView.decorations.from(execLineField, s => s.decos);
    const execGutter = gutter({
      class: 'cm-exec-gutter',
      lineMarker(view, line) {
        const state = view.state.field(execLineField);
        if (state.line < 1) return null;
        const execLine = view.state.doc.line(state.line);
        return line.from === execLine.from ? execMarker : null;
      },
    });

    const asm = StreamLanguage.define({
      token(s) {
        if (s.match(/;.*/)) return 'comment';
        if (s.match(ALL_MNEMONICS_RE)) return 'keyword';
        if (s.match(ALL_REGISTERS_RE)) return 'variableName';
        if (s.match(/\b0x[0-9A-Fa-f]+\b/)) return 'number';
        if (s.match(/\b[0-9]+(\.[0-9]+)?\b/)) return 'number';
        if (s.match(/'[^']*'/) || s.match(/"[^"]*"/)) return 'string';
        if (s.match(/\[.*?\]/)) return 'bracket';
        if (s.match(/\.?\w+:/)) return 'labelName';
        s.next(); return null;
      },
    });

    const sim8Theme = EditorView.theme({
      '&': { height: '100%', background: 'var(--t-canvas)', color: 'var(--t-mid)' },
      '.cm-scroller': { fontFamily: "'JetBrains Mono', monospace", fontSize: '12px', lineHeight: '1.6' },
      '.cm-gutters': { background: 'var(--t-nav)', borderRight: '1px solid var(--t-border)', color: 'var(--t-dim)', minWidth: '36px' },
      '.cm-gutter': { fontSize: '11px' },
      '.cm-activeLine': { background: 'rgba(204,85,0,0.04)' },
      '.cm-activeLineGutter': { background: 'rgba(204,85,0,0.06)', color: 'var(--t-dim)' },
      '.cm-cursor': { borderLeftColor: 'var(--a-orange)', borderLeftWidth: '1.5px' },
      '.cm-selectionBackground': { background: 'var(--a-orange-a20) !important' },
      '.cm-matchingBracket': { background: 'var(--a-orange-a20)', color: 'var(--a-orange) !important' },
      '.cm-searchMatch': { background: 'var(--a-orange-a20)' },
      '.cm-foldPlaceholder': { background: 'var(--t-surface)', border: '1px solid var(--t-border)', color: 'var(--t-dim)' },
      '.cm-tooltip': { background: 'var(--t-surface)', border: '1px solid var(--t-border)', color: 'var(--t-text)' },
      '.cm-panels': { background: 'var(--t-nav)', borderTop: '1px solid var(--t-border)', color: 'var(--t-mid)' },
    }, { dark: true });

    const sim8Highlight = HighlightStyle.define([
      { tag: tags.keyword,      class: 'cm-hl-kw' },
      { tag: tags.variableName, class: 'cm-hl-var' },
      { tag: tags.number,       class: 'cm-hl-num' },
      { tag: tags.string,       class: 'cm-hl-str' },
      { tag: tags.comment,      class: 'cm-hl-cmt' },
      { tag: tags.bracket,      class: 'cm-hl-brk' },
      { tag: tags.labelName,    class: 'cm-hl-lbl' },
    ]);

    cmScrollIntoView = EditorView.scrollIntoView;
    cmView = new EditorView({
      state: EditorState.create({ doc: defaultCode, extensions: [
        basicSetup, asm,
        sim8Theme,
        syntaxHighlighting(sim8Highlight),
        execLineField, execDecoExt, execGutter,
      ] }),
      parent: ct,
    });
  } catch (e) {
    console.warn('CodeMirror failed to load, using textarea fallback:', e);
    const ta = document.createElement('textarea');
    ta.style.cssText = "width:100%;height:100%;background:var(--t-canvas);color:var(--t-text);padding:16px;resize:none;outline:none;border:none;font-family:'JetBrains Mono',monospace;font-size:13px;tab-size:4;";
    ta.value = defaultCode;
    ta.spellcheck = false;
    ct.appendChild(ta);
  }
})();
