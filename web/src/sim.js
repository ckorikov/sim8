/**
 * sim8 v2 — Browser UI orchestrator.
 * Wires CPU, assembler, and all UI modules together.
 */

import { assemble, AsmError } from '../lib/asm.js';
import { CpuState } from '../lib/core.js';
import { BY_CODE_FP } from '../lib/isa.js';

import { cpu, asm, refreshColors } from './state.js';
import { renderCPU } from './ui/cpu.js';
import { renderFPU } from './ui/fpu.js';
import { renderMemory } from './ui/mem.js';
import { renderDisplay } from './ui/display.js';
import { renderLabels } from './ui/labels.js';
import { setupControls, stopRun, isRunning, updateRunBtnColor } from './controls.js';
import { initEditor, highlightExecLine, getEditorSource } from './editor.js';
import { flashWire, initWires, updateWireColors, WIRE_DATA, WIRE_FP, WIRE_IO } from './wires.js';
import { fitDiagram, setupSplitHandle, adjustBlockPositions } from './layout.js';

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

// ── Render all ─────────────────────────────────────────────────

function renderAll() {
  renderCPU(); renderFPU(); renderMemory(); renderDisplay();
  const line = asm.mapping[cpu.ip];
  highlightExecLine(line !== undefined ? line : -1);
}

// ── Assembly ───────────────────────────────────────────────────

function doAssemble(source) {
  const errEl = document.getElementById('asm-error');
  errEl.classList.add('hidden');
  errEl.textContent = '';

  try {
    const result = assemble(source);
    asm.codeLen = result.code.length;
    asm.labels = result.labels;
    asm.mapping = result.mapping;
    asm.instrStarts = new Set(Object.keys(result.mapping).map(Number));

    cpu.reset();
    cpu.load(result.code);

    renderLabels();
    renderAll();
    return true;
  } catch (e) {
    errEl.textContent = e instanceof AsmError ? e.message : 'Internal error: ' + e.message;
    errEl.classList.remove('hidden');
    return false;
  }
}

// ── Step / Reset ───────────────────────────────────────────────

function stepCPU() {
  if (cpu.state === CpuState.FAULT || cpu.state === CpuState.HALTED) return false;

  const prevIp = cpu.ip;
  const opcode = cpu.mem.get(prevIp);
  const wasRunning = cpu.step();

  if (BY_CODE_FP[opcode] !== undefined) {
    flashWire(WIRE_FP);
  } else {
    flashWire(WIRE_DATA);
  }
  flashWire(WIRE_IO);

  renderAll();
  return wasRunning;
}

function resetCPU() {
  if (isRunning()) stopRun();
  cpu.reset();
  if (asm.codeLen > 0) {
    const source = getEditorSource();
    if (source) {
      try {
        const result = assemble(source);
        cpu.load(result.code);
      } catch (e) {
        console.warn('Re-assembly on reset failed:', e.message);
      }
    }
  }
  highlightExecLine(-1);
  renderAll();
}

// ── Controls wiring ────────────────────────────────────────────

setupControls({
  onStep: () => stepCPU(),
  onReset: () => resetCPU(),
  renderCPU,
});

// ── Assemble button ────────────────────────────────────────────

document.getElementById('btn-assemble').addEventListener('click', () => {
  if (isRunning()) stopRun();
  doAssemble(getEditorSource());
});

// ── Theme toggle ───────────────────────────────────────────────

let isDark = true;
document.getElementById('btn-theme').addEventListener('click', () => {
  isDark = !isDark;
  document.documentElement.classList.toggle('light', !isDark);
  document.getElementById('theme-icon-dark').classList.toggle('hidden', isDark);
  document.getElementById('theme-icon-light').classList.toggle('hidden', !isDark);
  document.getElementById('theme-label').textContent = isDark ? 'light' : 'dark';

  refreshColors();
  renderAll();
  updateRunBtnColor();
  updateWireColors();
});

// ── Initialization ─────────────────────────────────────────────

renderAll();

requestAnimationFrame(() => {
  adjustBlockPositions(initWires);
});

setupSplitHandle(fitDiagram);

initEditor(document.getElementById('editor-container'), defaultCode);
