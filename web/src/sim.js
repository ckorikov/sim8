/**
 * sim8 v2 — Browser UI orchestrator.
 * Wires CPU, assembler, and all UI modules together.
 */

import { assemble, AsmError } from "../lib/asm.js";
import { CpuState } from "../lib/core.js";
import { BY_CODE_FP } from "../lib/isa.js";

import { cpu, asm, refreshColors, IO_BASE, PAGE_SIZE } from "./state.js";
import { renderCPU } from "./ui/cpu.js";
import { renderFPU } from "./ui/fpu.js";
import { renderMemory } from "./ui/mem.js";
import { renderDisplay } from "./ui/display.js";
import { renderLabels } from "./ui/labels.js";
import { setupControls, stopRun, isRunning, updateRunBtnColor } from "./controls.js";
import { initEditor, highlightExecLine, getEditorSource, getBreakpoints } from "./editor.js";
import { flashWire, initWires, updateWireColors, WIRE_DATA, WIRE_FP, WIRE_IO } from "./wires.js";
import { fitDiagram, setupSplitHandle, adjustBlockPositions } from "./layout.js";

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
    renderCPU();
    renderFPU();
    renderMemory();
    renderDisplay();
    const line = getExecLine();
    highlightExecLine(line !== undefined ? line : -1);
}

// ── Assembly ───────────────────────────────────────────────────

function doAssemble(source) {
    const errEl = document.getElementById("asm-error");
    errEl.classList.add("hidden");
    errEl.textContent = "";

    cpu.reset();
    asm.codeLen = 0;
    asm.labels = {};
    asm.mapping = {};
    asm.instrStarts = new Set();

    try {
        const result = assemble(source);
        asm.codeLen = result.code.length;
        asm.labels = result.labels;
        asm.mapping = result.mapping;
        asm.instrStarts = new Set(Object.keys(result.mapping).map(Number));
        cpu.load(result.code);
        renderLabels();
        renderAll();
        return true;
    } catch (e) {
        errEl.textContent = e instanceof AsmError ? `Line ${e.line}: ${e.message}` : "Internal error: " + e.message;
        errEl.classList.remove("hidden");
        renderLabels();
        renderAll();
        return false;
    }
}

// ── Step / Reset ───────────────────────────────────────────────

function ioChanged(snapshot) {
    for (let addr = IO_BASE; addr < PAGE_SIZE; addr++) {
        if (cpu.mem.get(addr) !== snapshot[addr - IO_BASE]) return true;
    }
    return false;
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

function resetCPU() {
    if (isRunning()) stopRun();
    doAssemble(getEditorSource());
    highlightExecLine(-1);
}

// ── Controls wiring ────────────────────────────────────────────

function getExecLine() {
    return asm.mapping[cpu.ip];
}

setupControls({
    onStep: stepCPU,
    onReset: resetCPU,
    renderCPU,
    getBreakpoints,
    getExecLine,
});

// ── Assemble button ────────────────────────────────────────────

document.getElementById("btn-assemble").addEventListener("click", () => {
    if (isRunning()) stopRun();
    doAssemble(getEditorSource());
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

initEditor(document.getElementById("editor-container"), defaultCode);
