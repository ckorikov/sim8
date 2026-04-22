/**
 * Layout management: block positioning, diagram scaling, split handle.
 */

import { cssVar } from "./state.js";
import { isTermActive } from "./ui/term.js";

const SPLIT_SNAP_RATIO = 0.05; // snap to fully collapsed within 5% of either edge
const BLOCK_GAP = 16; // gap between adjacent blocks (CPU↔FPU, VU↔Pad)
const IO_GAP = 24; // gap between Memory bottom and Display/Terminal top
const CONTAINER_PAD = 32; // bottom padding for diagram container

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
    cpuEl.style.left = memLeft + "px";
    fpuEl.style.left = memLeft + cpuEl.offsetWidth + BLOCK_GAP + "px";

    // ── Row 1: CPU + FPU at top, equal height ──
    cpuEl.style.top = topY + "px";
    fpuEl.style.top = topY + "px";
    const maxH = Math.max(cpuEl.offsetHeight, fpuEl.offsetHeight);
    cpuEl.style.minHeight = maxH + "px";
    fpuEl.style.minHeight = maxH + "px";

    const row1Bottom = topY + maxH;
    const fpuRight = memLeft + cpuEl.offsetWidth + BLOCK_GAP + fpuEl.offsetWidth;

    // ── Memory + Display/Terminal width = CPU left to FPU right ──
    const rowWidth = fpuRight - memLeft;
    memEl.style.width = rowWidth + "px";
    dispEl.style.width = rowWidth + "px";
    if (termEl) termEl.style.width = rowWidth + "px";

    // ── VU X: same gap as wireGap from Memory right ──
    if (vuEl) vuEl.style.left = fpuRight + wireGap + "px";

    // ── Row 2: Memory below bus corridor; VU aligned with row 1 top ──
    const row2Top = row1Bottom + wireGap;
    memEl.style.top = row2Top + "px";
    if (vuEl) vuEl.style.top = topY + "px";

    const memBottom = row2Top + memEl.offsetHeight;
    const vuBottom = vuEl ? topY + vuEl.offsetHeight : topY;

    // ── Display and terminal share the same position below memory ──
    const ioTop = memBottom + IO_GAP;
    dispEl.style.top = ioTop + "px";
    if (termEl) termEl.style.top = ioTop + "px";

    const padVisible = padEl && padEl.style.display !== "none";
    if (padVisible) {
        padEl.style.left = fpuRight + wireGap + "px";
        padEl.style.top = vuBottom + BLOCK_GAP + "px";
    }

    // ── Active I/O element for height calculation ──
    const activeIoEl = isTermActive() ? termEl : dispEl;

    const container = document.getElementById("diagram-container");
    let bottomEdge = parseInt(activeIoEl.style.top) + activeIoEl.offsetHeight;
    if (vuEl) bottomEdge = Math.max(bottomEdge, vuBottom);
    if (padVisible && padEl) bottomEdge = Math.max(bottomEdge, parseInt(padEl.style.top) + padEl.offsetHeight);

    container.style.height = bottomEdge + CONTAINER_PAD + "px";
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
    container.style.marginBottom = -(1 - scale) * natH + "px";
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
        left.style.width = targetW + "px";
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
