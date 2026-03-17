/**
 * sim8 v2 — Browser UI orchestrator.
 * Wires CPU, assembler, and all UI modules together.
 */

import { assembleAsync, AsmError } from "../lib/asm.js";
import { CpuState } from "../lib/core.js";
import { BY_CODE_FP } from "../lib/isa.js";

import { cpu, asm, refreshColors, IO_BASE, PAGE_SIZE } from "./state.js";
import { renderCPU } from "./ui/cpu.js";
import { renderFPU } from "./ui/fpu.js";
import { renderMemory } from "./ui/mem.js";
import { renderDisplay } from "./ui/display.js";
import { renderLabels } from "./ui/labels.js";
import { setupControls, stopRun, isRunning, updateRunBtnColor } from "./controls.js";
import { initEditor, highlightExecLine, clearExecLine, showDiagnostic, clearDiagnostics } from "./editor.js";
import { initTabs, saveCurrentTab, getVirtualFiles, getMainSource, switchTabForExec } from "./tabs.js";
import { breakpoints } from "./breakpoints.js";
import { flashWire, initWires, updateWireColors, WIRE_DATA, WIRE_FP, WIRE_IO } from "./wires.js";
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
    renderMemory();
    renderDisplay();
    showExecLine();
}

// ── Assembly ───────────────────────────────────────────────────

async function doAssemble() {
    saveCurrentTab();
    const errEl = document.getElementById("asm-error");
    errEl.classList.add("hidden");
    errEl.textContent = "";
    clearDiagnostics();

    cpu.reset();
    asm.codeLen = 0;
    asm.labels = {};
    asm.mapping = {};
    asm.lineMap = null;
    asm.instrStarts = new Set();
    asm.labelAddrs = new Set();
    asm.labelNames = new Map();

    try {
        const result = await assembleAsync(getMainSource(), 2, getVirtualFiles());
        asm.codeLen = result.code.length;
        asm.labels = result.labels;
        asm.mapping = result.mapping;
        asm.lineMap = result.lineMap;
        asm.instrStarts = new Set(Object.keys(result.mapping).map(Number));
        const allLabels = Object.entries(result.labels);
        asm.labelAddrs = new Set(allLabels.map(([, v]) => v));
        asm.labelNames = new Map(allLabels.map(([n, v]) => [v, n]));
        cpu.load(result.code);
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

function ioChanged(snapshot) {
    return snapshot.some((v, i) => cpu.mem.get(IO_BASE + i) !== v);
}

function stepCPU() {
    if (cpu.state === CpuState.FAULT || cpu.state === CpuState.HALTED) return 0;

    const prevCycles = cpu.cycles;
    const opcode = cpu.mem.get(cpu.ip);

    const ioSnap = new Uint8Array(PAGE_SIZE - IO_BASE);
    for (let i = 0; i < ioSnap.length; i++) ioSnap[i] = cpu.mem.get(IO_BASE + i);

    const wasRunning = cpu.step();

    if (BY_CODE_FP[opcode] !== undefined) {
        flashWire(WIRE_FP);
    } else {
        flashWire(WIRE_DATA);
    }
    if (ioChanged(ioSnap)) flashWire(WIRE_IO);

    renderAll();
    return wasRunning ? cpu.cycles - prevCycles : 0;
}

async function resetCPU() {
    if (isRunning()) stopRun();
    await doAssemble();
}

// ── Controls wiring ────────────────────────────────────────────

function getExecLine() {
    return asm.mapping[cpu.ip];
}

setupControls({
    onStep: stepCPU,
    onReset: resetCPU,
    renderCPU,
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

let isDark = localStorage.getItem("theme") !== "light";
applyTheme(isDark);
refreshColors();

document.getElementById("btn-theme").addEventListener("click", () => {
    isDark = !isDark;
    localStorage.setItem("theme", isDark ? "dark" : "light");
    applyTheme(isDark);
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

initEditor(document.getElementById("editor-container"), "").then(() => {
    initTabs();
});
