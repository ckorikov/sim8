/**
 * sim8 v3 — Browser UI orchestrator.
 * Wires CPU, assembler, and all UI modules together.
 */

import { assembleAsync, AsmError } from "../lib/asm.js";
import { CpuState } from "../lib/core.js";
import { BY_CODE_FP, BY_CODE_VU } from "../lib/isa.js";
import { cpu, asm, pad, refreshColors, IO_BASE, PAGE_SIZE } from "./state.js";
import { renderCPU } from "./ui/cpu.js";
import { renderFPU } from "./ui/fpu.js";
import { renderVU } from "./ui/vu.js";
import { renderMemory } from "./ui/mem.js";
import { renderDisplay } from "./ui/display.js";
import { renderPad, initPad } from "./ui/pad.js";
import { renderLabels } from "./ui/labels.js";
import { onToggle } from "./ui/marker-toggle.js";
import { setupControls, stopRun, isRunning, updateRunBtnColor } from "./controls.js";
import { initEditor, highlightExecLine, clearExecLine, showDiagnostic, clearDiagnostics } from "./editor.js";
import { initTabs, saveCurrentTab, getVirtualFiles, getMainSource, switchTabForExec } from "./tabs.js";
import { breakpoints } from "./breakpoints.js";
import { flashWire, initWires, updateWireColors, WIRE_DATA, WIRE_FP, WIRE_VU_A, WIRE_IO, WIRE_PAD } from "./wires.js";
import { fitDiagram, setupSplitHandle, adjustBlockPositions } from "./layout.js";

// ── Render all ─────────────────────────────────────────────────

function showExecLine() {
    const flatLine = getExecLine();
    if (flatLine === undefined) {
        clearExecLine();
        return;
    }
    const loc = asm.lineMap?.get(flatLine);
    if (loc) {
        switchTabForExec(loc.file);
        highlightExecLine(loc.line);
    } else {
        highlightExecLine(flatLine);
    }
}

function renderAll() {
    renderCPU();
    renderFPU();
    renderVU(cpu.vu);
    renderMemory();
    renderDisplay();
    renderPad();
    showExecLine();
}

onToggle(() => {
    renderCPU();
    renderVU(cpu.vu);
    renderMemory();
});

// ── Assembly ───────────────────────────────────────────────────

async function doAssemble() {
    saveCurrentTab();
    const errEl = document.getElementById("asm-error");
    errEl.classList.add("hidden");
    errEl.textContent = "";
    clearDiagnostics();

    cpu.reset();
    asm.labels = {};
    asm.mapping = {};
    asm.lineMap = null;
    asm.lastCode = null;
    asm.lastUsedBytes = 0;
    asm.instrStarts = new Set();
    asm.labelAddrs = new Set();
    asm.labelNames = new Map();

    try {
        const result = await assembleAsync(getMainSource(), 3, getVirtualFiles());
        asm.labels = result.labels;
        asm.mapping = result.mapping;
        asm.lineMap = result.lineMap;
        asm.lastCode = result.code;
        asm.lastUsedBytes = result.usedBytes;
        asm.instrStarts = new Set(Object.keys(result.mapping).map(Number));
        const allLabels = Object.entries(result.labels);
        asm.labelAddrs = new Set(allLabels.map(([, v]) => v));
        asm.labelNames = new Map(allLabels.map(([n, v]) => [v, n]));
        cpu.load(result.code, result.usedBytes);
        renderLabels();
        renderAll();
        return true;
    } catch (e) {
        errEl.textContent = e instanceof AsmError ? String(e) : "Internal error: " + e.message;
        errEl.classList.remove("hidden");
        if (e instanceof AsmError && e.line >= 1) showDiagnostic(e.line, e.message);
        renderLabels();
        renderAll();
        return false;
    }
}

// ── Step / Reset ───────────────────────────────────────────────

const _ioSnap = new Uint8Array(PAGE_SIZE - IO_BASE);

function ioChanged() {
    return _ioSnap.some((v, i) => cpu.mem.get(IO_BASE + i) !== v);
}

let _padChecksum = 0;

function padChecksum() {
    let s = 0;
    const len = pad.end - pad.start;
    for (let i = 0; i < len; i++) s += cpu.mem.get(pad.start + i);
    return s;
}

function padChanged() {
    const cs = padChecksum();
    if (cs !== _padChecksum) {
        _padChecksum = cs;
        return true;
    }
    return false;
}

function _activeWires(cpuDid, vuDid, opcode) {
    const wires = [];
    if (vuDid) wires.push(WIRE_VU_A);
    if (cpuDid) {
        if (BY_CODE_VU[opcode] !== undefined) {
            wires.push(WIRE_DATA, WIRE_VU_A);
        } else if (BY_CODE_FP[opcode] !== undefined) {
            wires.push(WIRE_FP);
        } else {
            wires.push(WIRE_DATA);
        }
    }
    if (ioChanged()) wires.push(WIRE_IO);
    if (pad.visible && padChanged()) wires.push(WIRE_PAD);
    return wires;
}

function stepCPU() {
    if (cpu.state === CpuState.FAULT) return 0;

    for (let i = 0; i < _ioSnap.length; i++) _ioSnap[i] = cpu.mem.get(IO_BASE + i);
    if (pad.visible) _padChecksum = padChecksum();

    const opcode = cpu.mem.get(cpu.ip);

    // VU ticks first — newly issued commands appear in queue for 1 UI frame
    const vuDid = cpu.vuTick();
    const cpuDid = cpu.step();

    if (!cpuDid && !vuDid && !cpu.vuWaiting) return 0;

    for (const w of _activeWires(cpuDid, vuDid, opcode)) flashWire(w);

    renderAll();
    return 1;
}

function resetCPU() {
    if (isRunning()) stopRun();
    if (asm.lastCode) {
        cpu.load(asm.lastCode, asm.lastUsedBytes);
    } else {
        cpu.reset();
    }
    renderAll();
}

// ── Controls wiring ────────────────────────────────────────────

function getExecLine() {
    return asm.mapping[cpu.ip];
}

setupControls({
    onStep: stepCPU,
    onReset: resetCPU,
    renderAll,
    checkBp: (flatLine) => breakpoints.checkFlat(flatLine, asm.lineMap),
    getExecLine,
});

// ── Assemble button ────────────────────────────────────────────

document.getElementById("btn-assemble").addEventListener("click", () => {
    if (isRunning()) stopRun();
    doAssemble();
});

// ── Theme toggle ───────────────────────────────────────────────

function applyTheme(dark) {
    document.documentElement.classList.toggle("light", !dark);
    document.getElementById("theme-icon-dark").classList.toggle("hidden", dark);
    document.getElementById("theme-icon-light").classList.toggle("hidden", !dark);
    document.getElementById("theme-label").textContent = dark ? "light" : "dark";
}

let isDark = localStorage.getItem("sim8-theme") !== "light";
applyTheme(isDark);
refreshColors();

document.getElementById("btn-theme").addEventListener("click", () => {
    isDark = !isDark;
    localStorage.setItem("sim8-theme", isDark ? "dark" : "light");
    applyTheme(isDark);
    refreshColors();
    renderAll();
    updateRunBtnColor();
    updateWireColors();
});

// ── Initialization ─────────────────────────────────────────────

renderAll();

initPad(
    () => adjustBlockPositions(initWires),
    () => renderMemory(),
);

requestAnimationFrame(() => {
    adjustBlockPositions(initWires);
});

setupSplitHandle(fitDiagram);

initEditor(document.getElementById("editor-container"), "").then(() => {
    initTabs();
});
