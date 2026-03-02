/**
 * Layout management: block positioning, diagram scaling, split handle.
 */

import { cssVar } from './state.js';

export function adjustBlockPositions(initWiresFn) {
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

  initWiresFn();
}

export function fitDiagram() {
  const section = document.getElementById('diagram-section');
  const container = document.getElementById('diagram-container');
  const natW = parseInt(cssVar('--s-diagram-w')) || 840;
  const availW = section.clientWidth - 32;
  const scale = Math.min(availW / natW, 1);
  container.style.transform = `scale(${scale})`;
  const natH = parseInt(container.style.height) || container.offsetHeight;
  container.style.marginBottom = (-(1 - scale) * natH) + 'px';
}

export function setupSplitHandle(onResize) {
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
    onResize();
  });

  window.addEventListener('mouseup', () => {
    if (!dragging) return;
    dragging = false;
    handle.classList.remove('active');
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
  });

  window.addEventListener('resize', onResize);
  requestAnimationFrame(onResize);
}
