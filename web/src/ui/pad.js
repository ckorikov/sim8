/**
 * Pad block: 28×28 pixel grid mapped to CPU memory.
 * Bidirectional: mouse drawing writes to memory, program writes update the canvas.
 */

import { cpu, pad, PAGE_SIZE } from "../state.js";

const MODES = {
    8: { w: 8, h: 8, px: 21 },
    16: { w: 16, h: 16, px: 10 },
    28: { w: 28, h: 28, px: 6 },
};
const DEFAULT_PAGE = 1;

const elBlock = document.getElementById("blk-pad");
const elCanvas = document.getElementById("pad-canvas");
const elPage = document.getElementById("pad-page");
const elAddr = document.getElementById("pad-addr");
const elClear = document.getElementById("pad-clear");
const elToggle = document.getElementById("btn-pad");
const elSize = document.getElementById("pad-size");

const ctx = elCanvas.getContext("2d");

let padW = 28;
let padH = 28;
let padSize = padW * padH;
let PX = MODES[28].px;

function setMode(size) {
    const m = MODES[size];
    padW = m.w;
    padH = m.h;
    PX = m.px;
    padSize = padW * padH;
    elCanvas.width = padW * PX;
    elCanvas.height = padH * PX;
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

// Initialize shared state
applyPadState();
syncInputs();

function getDrawValue() {
    return 255;
}

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
    const scaleX = elCanvas.width / rect.width;
    const scaleY = elCanvas.height / rect.height;
    const x = Math.floor(((e.clientX - rect.left) * scaleX) / PX);
    const y = Math.floor(((e.clientY - rect.top) * scaleY) / PX);
    if (x < 0 || x >= padW || y < 0 || y >= padH) return null;
    return { x, y };
}

function getBgStyle() {
    return getComputedStyle(document.documentElement).getPropertyValue("--t-bg").trim();
}

function getFgStyle() {
    return getComputedStyle(document.documentElement).getPropertyValue("--a-green").trim();
}

function paintCell(cx, cy, val) {
    const x = cx * PX;
    const y = cy * PX;
    ctx.fillStyle = getBgStyle();
    ctx.fillRect(x, y, PX, PX);
    if (val > 0) {
        ctx.globalAlpha = val / 255;
        ctx.fillStyle = getFgStyle();
        ctx.fillRect(x, y, PX, PX);
        ctx.globalAlpha = 1;
    }
}

function paint(cell) {
    if (!cell) return;
    const addr = pad.start + cell.y * padW + cell.x;
    const val = getDrawValue();
    cpu.mem.set(addr, val);
    paintCell(cell.x, cell.y, val);
}

export function renderPad() {
    if (!pad.visible) return;
    const base = pad.start;
    const bg = getBgStyle();
    const fg = getFgStyle();
    for (let y = 0; y < padH; y++) {
        for (let x = 0; x < padW; x++) {
            const v = cpu.mem.get(base + y * padW + x);
            const px = x * PX;
            const py = y * PX;
            ctx.fillStyle = bg;
            ctx.fillRect(px, py, PX, PX);
            if (v > 0) {
                ctx.globalAlpha = v / 255;
                ctx.fillStyle = fg;
                ctx.fillRect(px, py, PX, PX);
                ctx.globalAlpha = 1;
            }
        }
    }
}

function clearPad() {
    cpu.mem.reset();
    renderPad();
    if (_onSync) _onSync();
}

const elMemPort = document.getElementById("port-mem-right-pad");

function togglePad() {
    pad.visible = !pad.visible;
    elBlock.style.display = pad.visible ? "" : "none";
    elMemPort.style.display = pad.visible ? "" : "none";
    elToggle.style.color = pad.visible ? "var(--a-purple)" : "var(--t-dim)";
    if (pad.visible) renderPad();
}

let _onLayout = null;

export function initPad(onLayout, onSync) {
    _onLayout = onLayout;
    _onSync = onSync;

    elCanvas.addEventListener("mousedown", (e) => {
        e.preventDefault();
        drawing = true;
        paint(cellFromEvent(e));
    });

    elCanvas.addEventListener("mousemove", (e) => {
        if (!drawing) return;
        paint(cellFromEvent(e));
    });

    elCanvas.addEventListener("mouseup", () => {
        if (drawing) {
            drawing = false;
            if (_onSync) _onSync();
        }
    });

    elCanvas.addEventListener("mouseleave", () => {
        if (drawing) {
            drawing = false;
            if (_onSync) _onSync();
        }
    });

    elClear.addEventListener("click", clearPad);

    elSize.addEventListener("change", () => {
        setMode(parseInt(elSize.value, 10));
        renderPad();
        if (_onLayout) _onLayout();
        if (_onSync) _onSync();
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
