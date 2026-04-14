/**
 * X6 wire diagram: initialization, flash animation, theme sync.
 *
 * 3-column layout: CPU (left) | FPU (middle) | VU (right) in row 1.
 * Γ-bus: horizontal segment below row-1, vertical segment between FPU and VU.
 * Horizontal bus: from Memory left to BUS_X at BUS_Y (midpoint between row-1
 *   bottom and Memory top). CPU and FPU both drop vertical wires to BUS_Y.
 * Vertical bus: from VU top down through VU/PAD stub connections.
 * BUS_X: midpoint between FPU right and VU left (equal 28px clearance each).
 *
 * Wire indices (for flashWire):
 *   0 WIRE_DATA  — CPU bottom → horizontal bus (vertical drop, yellow)
 *   1 WIRE_FP    — FPU bottom → horizontal bus (vertical drop, orange)
 *   2 WIRE_VU_A  — VU left ← vertical bus (horizontal stub, yellow)
 *   3 WIRE_IO    — Memory bottom → Display (i/o)
 *   4 WIRE_PAD   — Pad left ← vertical bus (horizontal stub, purple)
 */

import { colors, pad } from "./state.js";

const WIRE_FLASH_MS = 350;
export const WIRE_DATA = 0;
export const WIRE_FP = 1;
export const WIRE_VU_A = 2;
export const WIRE_IO = 3;
export const WIRE_PAD = 4;

// SVG bus line elements — updated on theme change
let _busLines = [];

export function flashWire(idx) {
    const edge = document.querySelectorAll("#wire-canvas .x6-edge")[idx];
    if (!edge) return;
    edge.classList.add("wire-active");
    setTimeout(() => edge.classList.remove("wire-active"), WIRE_FLASH_MS);
}

export function updateWireColors() {
    document.querySelectorAll("#wire-canvas rect[rx]").forEach((r) => r.setAttribute("fill", colors.canvas));
    const c = colors.yl;
    document.querySelectorAll("#wire-canvas .x6-edge").forEach((edge) => {
        const line = edge.querySelector("path[stroke-dasharray]");
        if (line) line.setAttribute("stroke", c);
        edge.querySelectorAll("marker path, marker polygon").forEach((m) => {
            m.setAttribute("fill", c);
            m.setAttribute("stroke", c);
        });
        const txt = edge.querySelector("text");
        if (txt) txt.setAttribute("fill", c);
    });
    _busLines.forEach((el) => el.setAttribute("stroke", colors.yl));
}

export function initWires() {
    _busLines = [];

    if (typeof X6 === "undefined") {
        document.getElementById("wire-canvas").innerHTML =
            '<div style="position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);color:#cc4444;">X6 failed to load</div>';
        return;
    }

    const container = document.getElementById("diagram-container");
    const cRect = container.getBoundingClientRect();
    const canvas = document.getElementById("wire-canvas");
    canvas.innerHTML = "";
    const cW = container.offsetWidth;
    const cH = container.offsetHeight;
    canvas.style.width = cW + "px";
    canvas.style.height = cH + "px";

    const { Graph } = X6;
    const graph = new Graph({
        container: canvas,
        width: cW,
        height: cH,
        background: false,
        grid: false,
        interacting: false,
    });

    function portPos(portId) {
        const port = document.getElementById(portId);
        const pr = port.getBoundingClientRect();
        return {
            x: Math.round(pr.left - cRect.left + pr.width / 2),
            y: Math.round(pr.top - cRect.top + pr.height / 2),
        };
    }

    // ── Γ bus geometry: 3-column layout (CPU | FPU | VU in row 1) ──
    // Horizontal bus below row 1; vertical bus between FPU and VU columns.
    const cpuR = document.getElementById("blk-cpu").getBoundingClientRect();
    const memR = document.getElementById("blk-mem").getBoundingClientRect();
    const fpuR = document.getElementById("blk-fpu").getBoundingClientRect();
    const hasVu = !!document.getElementById("blk-vu");
    const vuR = hasVu ? document.getElementById("blk-vu").getBoundingClientRect() : null;

    const cpuBottomY = Math.round(cpuR.bottom - cRect.top);
    const fpuBottomY = Math.round(fpuR.bottom - cRect.top);
    const memTopY = Math.round(memR.top - cRect.top);
    const memLeftX = Math.round(memR.left - cRect.left);
    const memRightX = Math.round(memR.right - cRect.left);
    const vuLeftX = vuR ? Math.round(vuR.left - cRect.left) : memRightX + 56;

    // BUS_Y: midpoint between row-1 bottom and Memory top → equal clearance
    const row1BottomY = Math.max(cpuBottomY, fpuBottomY);
    const BUS_Y = Math.round((row1BottomY + memTopY) / 2);
    // BUS_X: midpoint between Memory right and VU left → equal clearance
    const BUS_X = Math.round((memRightX + vuLeftX) / 2);

    // Vertical bus: upper branch fixed by VU port, lower branch mirrors or extends for Pad
    const vuPortY = hasVu ? Math.round(vuR.top - cRect.top + vuR.height * 0.5) : BUS_Y;
    const upperArm = BUS_Y - Math.min(BUS_Y, vuPortY);
    let lowerArm = vuR ? Math.round(vuR.bottom - cRect.top) - BUS_Y : upperArm;
    if (pad.visible && document.getElementById("blk-pad")) {
        const padR = document.getElementById("blk-pad").getBoundingClientRect();
        lowerArm = Math.max(lowerArm, Math.round(padR.bottom - cRect.top) - BUS_Y);
    }
    // Without Pad, mirror arms; with Pad, lower extends independently
    if (!pad.visible) lowerArm = Math.max(lowerArm, upperArm);
    const busTop = BUS_Y - upperArm;
    const busBottom = BUS_Y + lowerArm;

    // ── Draw Γ bus as SVG lines, inserted behind X6 edges ──
    const svgEl = canvas.querySelector("svg");
    const busGroup = document.createElementNS("http://www.w3.org/2000/svg", "g");
    const defs = svgEl.querySelector("defs");
    if (defs) defs.insertAdjacentElement("afterend", busGroup);
    else svgEl.insertBefore(busGroup, svgEl.firstChild);

    function addBusLine(x1, y1, x2, y2) {
        const line = document.createElementNS("http://www.w3.org/2000/svg", "line");
        line.setAttribute("x1", x1);
        line.setAttribute("y1", y1);
        line.setAttribute("x2", x2);
        line.setAttribute("y2", y2);
        line.setAttribute("stroke", colors.yl);
        line.setAttribute("stroke-width", "4");
        line.setAttribute("stroke-linecap", "round");
        busGroup.appendChild(line);
        _busLines.push(line);
    }

    // Horizontal bus: from Memory left to BUS_X corner (Γ horizontal bar)
    addBusLine(memLeftX, BUS_Y, BUS_X, BUS_Y);
    // Vertical bus: from row-1 top down to PAD/VU bottom (Γ vertical bar)
    addBusLine(BUS_X, busTop, BUS_X, busBottom);

    // ── Helper: add a dashed X6 edge between two { x, y } points ──
    function addWire(from, to, color, label, opts = {}) {
        const bidir = opts.bidir !== false;
        const labelOffset = opts.labelOffset || 0;
        const strokeWidth = opts.strokeWidth ?? 1.5;
        const lineAttrs = {
            stroke: color,
            strokeWidth,
            strokeDasharray: "6 3",
            targetMarker: { name: "block", width: 6, height: 4, fill: color, stroke: color },
        };
        if (bidir) lineAttrs.sourceMarker = { name: "block", width: 6, height: 4, fill: color, stroke: color };

        graph.addEdge({
            source: { x: from.x, y: from.y },
            target: { x: to.x, y: to.y },
            vertices: opts.vertices ?? [],
            router: { name: "normal" },
            connector: { name: "rounded", args: { radius: 8 } },
            attrs: { line: lineAttrs },
            labels: label
                ? [
                      {
                          position: { distance: 0.5, offset: labelOffset },
                          attrs: {
                              text: {
                                  text: label,
                                  fontSize: 9,
                                  fontFamily: "'JetBrains Mono',monospace",
                                  fill: color,
                                  letterSpacing: "0.05em",
                              },
                              rect: { fill: colors.canvas, rx: 2, ry: 2 },
                          },
                      },
                  ]
                : [],
        });
    }

    // ── Wire 0: WIRE_DATA — CPU bottom → horizontal bus (vertical drop) ──
    const cpuBot = portPos("port-cpu-bottom");
    addWire(cpuBot, { x: cpuBot.x, y: BUS_Y }, colors.yl, null, { bidir: false });

    // ── Wire 1: WIRE_FP — FPU bottom → horizontal bus (vertical drop) ──
    const fpuBot = portPos("port-fpu-bottom");
    addWire(fpuBot, { x: fpuBot.x, y: BUS_Y }, colors.yl, null, { bidir: false });

    // ── Wire 2: WIRE_VU_A — VU left ← vertical bus (horizontal stub) ──
    if (hasVu) {
        const vuLeft = portPos("port-vu-left-a");
        addWire({ x: BUS_X, y: vuLeft.y }, vuLeft, colors.yl, null, { bidir: true });
    }

    // ── Wire 3: WIRE_IO — Memory bottom → Display top ──
    const memBot = portPos("port-mem-bottom");
    const dispTop = portPos("port-disp-top");
    addWire(memBot, dispTop, colors.yl, "i/o", { bidir: false, labelOffset: 20 });

    // ── Wire 4: WIRE_PAD — Pad left ← vertical bus (horizontal stub) ──
    if (pad.visible && document.getElementById("port-pad-left")) {
        const padLeft = portPos("port-pad-left");
        addWire({ x: BUS_X, y: padLeft.y }, padLeft, colors.yl, null, { bidir: true });
    }
}
