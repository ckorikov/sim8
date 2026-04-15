/**
 * Pad block: pixel grid (8×8, 16×16, 28×28, 64×64) mapped to CPU memory.
 * Bidirectional: mouse drawing writes to memory, program writes update the canvas.
 */

import { cpu, pad, colors, PAGE_SIZE } from "../state.js";

const VALID_SIZES = [8, 16, 28, 64];
const CANVAS_SIZES = { 8: 192, 16: 192, 28: 168, 64: 192 };
const DRAW_VALUE = 255;
const DEFAULT_PAGE = 1;

const elBlock = document.getElementById("blk-pad");
const elCanvas = document.getElementById("pad-canvas");
const elPage = document.getElementById("pad-page");
const elAddr = document.getElementById("pad-addr");
const elClear = document.getElementById("pad-clear");
const elToggle = document.getElementById("btn-pad");
const elSizeTabs = document.getElementById("pad-size-tabs");

const ctx = elCanvas.getContext("2d");

let gridSize = 28;
let padSize = gridSize * gridSize;
let canvasSize = CANVAS_SIZES[gridSize];
let PX = canvasSize / gridSize;

function setMode(size) {
    gridSize = size;
    canvasSize = CANVAS_SIZES[size];
    PX = canvasSize / gridSize;
    padSize = gridSize * gridSize;
    elCanvas.width = canvasSize;
    elCanvas.height = canvasSize;
    applyPadState();
}

let drawing = false;
let _onSync = null;

let padPage = DEFAULT_PAGE;
let padOffset = 0;

function applyPadState() {
    const addr = padPage * PAGE_SIZE + padOffset;
    pad.start = addr;
    pad.end = addr + padSize;
}

function syncInputs() {
    elPage.value = padPage;
    elAddr.value = padOffset;
}

applyPadState();
syncInputs();

function parsePageInput() {
    const v = parseInt(elPage.value, 10);
    if (!Number.isFinite(v) || v < 0 || v > 255) return;
    if (v * PAGE_SIZE + padOffset + padSize > 0x10000) return;
    padPage = v;
    applyPadState();
}

function parseAddrInput() {
    const v = parseInt(elAddr.value, 10);
    if (!Number.isFinite(v) || v < 0 || v > 255) return;
    if (padPage * PAGE_SIZE + v + padSize > 0x10000) return;
    padOffset = v;
    applyPadState();
}

function cellFromEvent(e) {
    const rect = elCanvas.getBoundingClientRect();
    const cellPx = rect.width / gridSize;
    const x = Math.floor((e.clientX - rect.left) / cellPx);
    const y = Math.floor((e.clientY - rect.top) / cellPx);
    if (x < 0 || x >= gridSize || y < 0 || y >= gridSize) return null;
    return { x, y };
}

function paintCell(cx, cy, val) {
    const x = cx * PX;
    const y = cy * PX;
    ctx.fillStyle = colors.canvas;
    ctx.fillRect(x, y, PX, PX);
    if (val > 0) {
        ctx.globalAlpha = val / 255;
        ctx.fillStyle = colors.gr;
        ctx.fillRect(x, y, PX, PX);
        ctx.globalAlpha = 1;
    }
}

function paint(cell) {
    if (!cell) return;
    const addr = pad.start + cell.y * gridSize + cell.x;
    cpu.mem.set(addr, DRAW_VALUE);
    paintCell(cell.x, cell.y, DRAW_VALUE);
}

export function renderPad() {
    if (!pad.visible) return;
    const base = pad.start;
    for (let y = 0; y < gridSize; y++) {
        for (let x = 0; x < gridSize; x++) {
            paintCell(x, y, cpu.mem.get(base + y * gridSize + x));
        }
    }
}

function clearPad() {
    for (let i = pad.start; i < pad.end; i++) cpu.mem.set(i, 0);
    ctx.fillStyle = colors.canvas;
    ctx.fillRect(0, 0, canvasSize, canvasSize);
    renderPad();
    if (_onSync) _onSync();
}

function applyPadVisible() {
    elBlock.style.display = pad.visible ? "" : "none";
    elToggle.style.color = pad.visible ? "var(--a-purple)" : "var(--t-dim)";
    if (pad.visible) renderPad();
}

function togglePad() {
    pad.visible = !pad.visible;
    localStorage.setItem("sim8-pad", pad.visible ? "on" : "off");
    applyPadVisible();
}

let _onLayout = null;

export function initPad(onLayout, onSync) {
    _onLayout = onLayout;
    _onSync = onSync;

    pad.visible = localStorage.getItem("sim8-pad") === "on";
    applyPadVisible();

    elCanvas.addEventListener("mousedown", (e) => {
        e.preventDefault();
        drawing = true;
        paint(cellFromEvent(e));
    });

    elCanvas.addEventListener("mousemove", (e) => {
        if (!drawing) return;
        paint(cellFromEvent(e));
    });

    const stopDrawing = () => {
        if (drawing) {
            drawing = false;
            if (_onSync) _onSync();
        }
    };
    elCanvas.addEventListener("mouseup", stopDrawing);
    elCanvas.addEventListener("mouseleave", stopDrawing);

    elClear.addEventListener("click", clearPad);

    elSizeTabs.addEventListener("click", (e) => {
        const t = e.target.closest("[data-padsize]");
        if (!t) return;
        const size = parseInt(t.dataset.padsize, 10);
        if (!VALID_SIZES.includes(size)) return;
        elSizeTabs.querySelectorAll(".ft").forEach((b) => b.classList.toggle("act", b === t));
        setMode(size);
        clearPad();
    });

    elPage.addEventListener("change", () => {
        parsePageInput();
        syncInputs();
        renderPad();
        if (_onSync) _onSync();
    });

    elAddr.addEventListener("change", () => {
        parseAddrInput();
        syncInputs();
        renderPad();
        if (_onSync) _onSync();
    });

    elToggle.addEventListener("click", () => {
        togglePad();
        if (_onLayout) _onLayout();
        if (_onSync) _onSync();
    });
}
