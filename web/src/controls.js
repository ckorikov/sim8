/**
 * Run/Step/Reset button management and execution timer.
 */

import { cpu, colors } from "./state.js";
import { CpuState } from "../lib/core.js";

const btnRun = document.getElementById("btn-run");
const btnStep = document.getElementById("btn-step");
const btnReset = document.getElementById("btn-reset");
const speedSel = document.getElementById("speed-select");
let runTimer = null;
let stepTimer = null;

let _onStep;
let _onReset;
let _onBatchEnd;
let _renderCPU;
let _checkBp;
let _getExecLine;
let _skipBpOnce = false;

export function updateRunBtnColor() {
    btnRun.style.color = btnRun.dataset.state === "run" ? colors.gr : colors.rd;
}

const BATCH_THRESHOLD = 128;

function getSpeedHz() {
    return parseInt(speedSel.value) || 4;
}

function setRunUI(running) {
    btnRun.dataset.state = running ? "stop" : "run";
    btnRun.querySelector("svg").innerHTML = running
        ? '<rect x="3" y="3" width="10" height="10"/>'
        : '<polygon points="3,1 13,8 3,15"/>';
    btnRun.querySelector("span").textContent = running ? "stop" : "run";
    updateRunBtnColor();
}

function tick() {
    const hz = getSpeedHz();
    const batch = hz > BATCH_THRESHOLD ? Math.round(hz / 60) : 1;

    for (let i = 0; i < batch; i++) {
        if (!_skipBpOnce) {
            const execLine = _getExecLine?.();
            if (_checkBp?.(execLine)) {
                stopRun();
                return;
            }
        }
        _skipBpOnce = false;
        let cost;
        try {
            cost = _onStep();
        } catch (e) {
            console.error("Step error:", e);
            stopRun();
            return;
        }
        if (!cost) {
            stopRun();
            return;
        }
    }
    _onBatchEnd?.();
    runTimer = setTimeout(tick, hz > BATCH_THRESHOLD ? 16 : Math.round(1000 / hz));
}

async function startRun() {
    if (runTimer) return;
    if (cpu.state === CpuState.HALTED || cpu.state === CpuState.FAULT) {
        await _onReset();
    }
    _skipBpOnce = true;
    setRunUI(true);
    tick();
}

export function stopRun() {
    if (stepTimer) {
        clearTimeout(stepTimer);
        stepTimer = null;
    }
    if (runTimer) {
        clearTimeout(runTimer);
        runTimer = null;
    }
    cpu.pause();
    setRunUI(false);
    _renderCPU();
}

export function isRunning() {
    return runTimer !== null;
}

export function setupControls({ onStep, onReset, onBatchEnd, renderAll, checkBp, getExecLine }) {
    _onStep = onStep;
    _onReset = onReset;
    _onBatchEnd = onBatchEnd;
    _renderCPU = renderAll;
    _checkBp = checkBp;
    _getExecLine = getExecLine;

    btnRun.addEventListener("click", () => {
        if (runTimer) stopRun();
        else startRun();
    });

    btnStep.addEventListener("click", () => {
        if (runTimer) stopRun();
        if (cpu.state === CpuState.FAULT) return;
        if (cpu.state === CpuState.HALTED) return;
        if (stepTimer) {
            clearTimeout(stepTimer);
            stepTimer = null;
        }
        // Skip BP check on step — user explicitly requested one step
        const cost = _onStep();
        _onBatchEnd?.();
        if (cpu.state === CpuState.RUNNING && cost > 0) {
            stepTimer = setTimeout(
                () => {
                    stepTimer = null;
                    if (!isRunning()) {
                        cpu.pause();
                        _renderCPU();
                    }
                },
                Math.round(1000 / getSpeedHz()),
            );
        }
    });

    btnReset.addEventListener("click", () => _onReset());

    speedSel.addEventListener("change", () => {
        if (runTimer) {
            clearTimeout(runTimer);
            runTimer = setTimeout(tick, Math.round(1000 / getSpeedHz()));
        }
    });
}
