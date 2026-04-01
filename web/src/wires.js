/**
 * X6 wire diagram: initialization, flash animation, theme sync.
 */

import { colors } from "./state.js";

const WIRE_FLASH_MS = 350;
export const WIRE_DATA = 0;
export const WIRE_FP = 1;
export const WIRE_IO = 2;
export const WIRE_VU_CMD = 3;
export const WIRE_VU_A = 4;
export const WIRE_VU_B = 5;

export function flashWire(idx) {
    const edge = document.querySelectorAll("#wire-canvas .x6-edge")[idx];
    if (!edge) return;
    edge.classList.add("wire-active");
    setTimeout(() => edge.classList.remove("wire-active"), WIRE_FLASH_MS);
}

export function updateWireColors() {
    document.querySelectorAll("#wire-canvas rect[rx]").forEach((r) => r.setAttribute("fill", colors.canvas));
    const wireColors = {
        [WIRE_DATA]: colors.yl,
        [WIRE_FP]: colors.or,
        [WIRE_IO]: colors.gr,
        [WIRE_VU_CMD]: colors.yl,
        [WIRE_VU_A]: colors.yl,
        [WIRE_VU_B]: colors.yl,
    };
    document.querySelectorAll("#wire-canvas .x6-edge").forEach((edge, i) => {
        const c = wireColors[i];
        if (!c) return;
        const line = edge.querySelector("path[stroke-dasharray]");
        if (line) line.setAttribute("stroke", c);
        edge.querySelectorAll("marker path, marker polygon").forEach((m) => {
            m.setAttribute("fill", c);
            m.setAttribute("stroke", c);
        });
        const txt = edge.querySelector("text");
        if (txt) txt.setAttribute("fill", c);
    });
}

export function initWires() {
    if (typeof X6 === "undefined") {
        document.getElementById("wire-canvas").innerHTML =
            '<div style="position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);color:#cc4444;">X6 failed to load</div>';
        return;
    }

    const container = document.getElementById("diagram-container");
    const cRect = container.getBoundingClientRect();
    const canvas = document.getElementById("wire-canvas");
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

    function bentVerts(from, to) {
        const dx = Math.abs(to.x - from.x);
        const dy = Math.abs(to.y - from.y);
        if (dx < 4 || dy < 4) return [];
        const midY = Math.round((from.y + to.y) / 2);
        return [
            { x: from.x, y: midY },
            { x: to.x, y: midY },
        ];
    }

    function addWire(fromId, toId, color, label, opts = {}) {
        const from = portPos(fromId);
        const to = portPos(toId);
        const bidir = opts.bidir !== false;
        const labelOffset = opts.labelOffset || 0;
        const lineAttrs = {
            stroke: color,
            strokeWidth: 1.5,
            strokeDasharray: "6 3",
            targetMarker: { name: "block", width: 6, height: 4, fill: color, stroke: color },
        };
        if (bidir) {
            lineAttrs.sourceMarker = { name: "block", width: 6, height: 4, fill: color, stroke: color };
        }

        const verts = opts.vertices ?? bentVerts(from, to);

        graph.addEdge({
            source: { x: from.x, y: from.y },
            target: { x: to.x, y: to.y },
            vertices: verts,
            router: { name: "normal" },
            connector: { name: "rounded", args: { radius: 8 } },
            attrs: { line: lineAttrs },
            labels: [
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
            ],
        });
    }

    const cpuBot = portPos("port-cpu-bottom");
    const memTop = portPos("port-mem-top");
    const dataBusY = memTop.y - 20;
    addWire("port-cpu-bottom", "port-mem-top", colors.yl, "data bus", {
        vertices: [
            { x: cpuBot.x, y: dataBusY },
            { x: memTop.x, y: dataBusY },
        ],
    });
    addWire("port-cpu-right", "port-fpu-left", colors.or, "fp bus", { labelOffset: -12 });
    addWire("port-mem-bottom", "port-disp-top", colors.gr, "i/o", { bidir: false, labelOffset: 20 });

    if (document.getElementById("port-vu-top")) {
        addWire("port-cpu-vu", "port-vu-top", colors.yl, "cmd bus", { labelOffset: 14 });
        addWire("port-mem-right-a", "port-vu-left-a", colors.yl, "vu bus", { vertices: [], labelOffset: -12 });
        addWire("port-mem-right-b", "port-vu-left-b", colors.yl, "", { vertices: [] });
    }
}
