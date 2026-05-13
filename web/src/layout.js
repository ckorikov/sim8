/**
 * Layout management: block positioning, diagram scaling, split handle.
 */

import { cssVar } from "./state.js";
import { isTermActive } from "./ui/term.js";

const SPLIT_SNAP_RATIO = 0.05; // snap to fully collapsed within 5% of either edge
const BLOCK_GAP = 16; // gap between adjacent blocks (CPU↔FPU, VU↔Pad)
const IO_GAP = 24; // gap between Memory bottom and Display/Terminal top
const CONTAINER_PAD = 32; // bottom padding for diagram container

const px = (n) => n + "px";

export function adjustBlockPositions(initWiresFn) {
    const cpuEl = document.getElementById("blk-cpu");
    const fpuEl = document.getElementById("blk-fpu");
    const memEl = document.getElementById("blk-mem");
    const vuEl = document.getElementById("blk-vu");
    const dispEl = document.getElementById("blk-disp");
    const termEl = document.getElementById("blk-term");
    const padEl = document.getElementById("blk-pad");
    const wireGap = parseInt(cssVar("--s-wire-gap")) || 56;
    const topY = parseInt(cssVar("--s-top-y")) || 32;

    // ── Horizontal: CPU+FPU left-aligned ──
    const memLeft = parseInt(cssVar("--s-cpu-x")) || 48;
    cpuEl.style.left = px(memLeft);
    fpuEl.style.left = px(memLeft + cpuEl.offsetWidth + BLOCK_GAP);

    // ── Row 1: CPU + FPU at top, equal height ──
    cpuEl.style.top = px(topY);
    fpuEl.style.top = px(topY);
    const maxH = Math.max(cpuEl.offsetHeight, fpuEl.offsetHeight);
    cpuEl.style.minHeight = px(maxH);
    fpuEl.style.minHeight = px(maxH);

    const row1Bottom = topY + maxH;
    const fpuRight = memLeft + cpuEl.offsetWidth + BLOCK_GAP + fpuEl.offsetWidth;

    // ── Memory + Display/Terminal width = CPU left to FPU right ──
    const rowWidth = fpuRight - memLeft;
    memEl.style.width = px(rowWidth);
    dispEl.style.width = px(rowWidth);
    if (termEl) termEl.style.width = px(rowWidth);

    // ── VU X: same gap as wireGap from Memory right ──
    if (vuEl) vuEl.style.left = px(fpuRight + wireGap);

    // ── Row 2: Memory below bus corridor; VU aligned with row 1 top ──
    const row2Top = row1Bottom + wireGap;
    memEl.style.top = px(row2Top);
    if (vuEl) vuEl.style.top = px(topY);

    const memBottom = row2Top + memEl.offsetHeight;
    const vuBottom = vuEl ? topY + vuEl.offsetHeight : topY;

    // ── Display and terminal share the same position below memory ──
    const ioTop = memBottom + IO_GAP;
    dispEl.style.top = px(ioTop);
    if (termEl) termEl.style.top = px(ioTop);

    const padVisible = padEl && padEl.style.display !== "none";
    if (padVisible) {
        padEl.style.left = px(fpuRight + wireGap);
        padEl.style.top = px(vuBottom + BLOCK_GAP);
    }

    // ── Active I/O element for height calculation ──
    const activeIoEl = isTermActive() ? termEl : dispEl;

    const container = document.getElementById("diagram-container");
    let bottomEdge = parseInt(activeIoEl.style.top) + activeIoEl.offsetHeight;
    if (vuEl) bottomEdge = Math.max(bottomEdge, vuBottom);
    if (padVisible && padEl) bottomEdge = Math.max(bottomEdge, parseInt(padEl.style.top) + padEl.offsetHeight);

    container.style.height = px(bottomEdge + CONTAINER_PAD);
    initWiresFn();
}

export function fitDiagram() {
    const section = document.getElementById("diagram-section");
    const container = document.getElementById("diagram-container");
    const natW = parseInt(cssVar("--s-diagram-w")) || 840;
    const availW = section.clientWidth - 32;
    const scale = Math.min(availW / natW, 1);
    container.style.transform = `scale(${scale})`;
    const natH = parseInt(container.style.height) || container.offsetHeight;
    container.style.marginBottom = px(-(1 - scale) * natH);
}

export function setupSplitHandle(onResize) {
    const handle = document.getElementById("split-handle");
    const left = document.getElementById("left-panel");
    let dragging = false;

    handle.addEventListener("mousedown", (e) => {
        e.preventDefault();
        dragging = true;
        handle.classList.add("active");
        document.body.style.cursor = "col-resize";
        document.body.style.userSelect = "none";
    });

    window.addEventListener("mousemove", (e) => {
        if (!dragging) return;
        const mainRect = left.parentElement.getBoundingClientRect();
        const maxLeftW = mainRect.width - handle.offsetWidth; // right collapsed: diagram = 0px
        const snapPx = mainRect.width * SPLIT_SNAP_RATIO;
        const x = e.clientX - mainRect.left;
        let targetW;
        if (x < snapPx) targetW = 0;
        else if (x > maxLeftW - snapPx) targetW = maxLeftW;
        else targetW = x;
        left.style.width = px(targetW);
        onResize();
    });

    window.addEventListener("mouseup", () => {
        if (!dragging) return;
        dragging = false;
        handle.classList.remove("active");
        document.body.style.cursor = "";
        document.body.style.userSelect = "";
    });

    window.addEventListener("resize", onResize);
    requestAnimationFrame(onResize);
}
