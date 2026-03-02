/**
 * Run/Step/Reset button management and execution timer.
 */

import { cpu, cssVar } from './state.js';
import { CpuState } from '../lib/core.js';

const btnRun = document.getElementById('btn-run');
const btnStep = document.getElementById('btn-step');
const btnReset = document.getElementById('btn-reset');
const speedSel = document.getElementById('speed-select');
let runTimer = null;

let _onStep, _onReset, _renderCPU;

export function updateRunBtnColor() {
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

function tick() {
  const cost = _onStep();
  if (!cost) { stopRun(); return; }
  runTimer = setTimeout(tick, getSpeedMs() * cost);
}

function startRun() {
  if (runTimer) return;
  if (cpu.state === CpuState.HALTED || cpu.state === CpuState.FAULT) {
    _onReset();
  }
  setRunUI(true);
  tick();
}

export function stopRun() {
  if (runTimer) { clearTimeout(runTimer); runTimer = null; }
  if (cpu.state === CpuState.RUNNING) {
    cpu.state = CpuState.IDLE;
  }
  setRunUI(false);
  _renderCPU();
}

export function isRunning() { return runTimer !== null; }

export function setupControls({ onStep, onReset, renderCPU }) {
  _onStep = onStep;
  _onReset = onReset;
  _renderCPU = renderCPU;

  btnRun.addEventListener('click', () => {
    if (runTimer) stopRun(); else startRun();
  });

  btnStep.addEventListener('click', () => {
    if (runTimer) stopRun();
    if (cpu.state === CpuState.HALTED || cpu.state === CpuState.FAULT) return;
    _onStep();
    if (cpu.state === CpuState.RUNNING) {
      cpu.state = CpuState.IDLE;
      _renderCPU();
    }
  });

  btnReset.addEventListener('click', () => _onReset());

  speedSel.addEventListener('change', () => {
    if (runTimer) { stopRun(); startRun(); }
  });
}
