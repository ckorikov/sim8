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

function cancelTimer(ref) {
    if (ref) clearTimeout(ref);
    return null;
}

function isCpuTerminated() {
    return cpu.state === CpuState.FAULT || cpu.state === CpuState.HALTED;
}

function getSpeedHz() {
    return parseInt(speedSel.value) || 4;
}

function batchSize(hz) {
    return hz > BATCH_THRESHOLD ? Math.round(hz / 60) : 1;
}

function tickDelay(hz) {
    return hz > BATCH_THRESHOLD ? 16 : Math.round(1000 / hz);
}

function _isBreakpointHit() {
    const execLine = _getExecLine?.();
    return !!_checkBp?.(execLine);
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

    for (let i = 0; i < batchSize(hz); i++) {
        if (!_skipBpOnce && _isBreakpointHit()) {
            stopRun();
            return;
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
    runTimer = setTimeout(tick, tickDelay(hz));
}

function startRun() {
    if (runTimer) return;
    if (isCpuTerminated()) {
        cpu.restart();
    }
    _skipBpOnce = true;
    setRunUI(true);
    tick();
}

export function stopRun() {
    stepTimer = cancelTimer(stepTimer);
    runTimer = cancelTimer(runTimer);
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
        if (isCpuTerminated()) return;
        stepTimer = cancelTimer(stepTimer);
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
            runTimer = cancelTimer(runTimer);
            runTimer = setTimeout(tick, tickDelay(getSpeedHz()));
        }
    });
}
