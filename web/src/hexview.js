/**
 * Hex dump renderer for binary file tabs.
 */

import { hex, printableChar } from "./state.js";

const BYTES_PER_ROW = 16;

/**
 * Render a Uint8Array as a plain-text hex dump string (used by tests).
 * Format per row: `OOOO  hh hh hh hh hh hh hh hh  hh hh hh hh hh hh hh hh  aaaaaaaaaaaaaaaa`
 * @param {Uint8Array} bytes
 * @returns {string}
 */
export function renderHex(bytes) {
    if (!bytes.length) return "";
    const lines = [];
    for (let offset = 0; offset < bytes.length; offset += BYTES_PER_ROW) {
        const row = bytes.subarray(offset, offset + BYTES_PER_ROW);
        const hexCells = [];
        const ascii = [];
        for (let i = 0; i < BYTES_PER_ROW; i++) {
            if (i < row.length) {
                hexCells.push(hex(row[i]));
                ascii.push(printableChar(row[i]) || ".");
            } else {
                hexCells.push("  ");
                ascii.push(" ");
            }
        }
        const hex1 = hexCells.slice(0, 8).join(" ");
        const hex2 = hexCells.slice(8).join(" ");
        lines.push(`${hex(offset, 4)}  ${hex1}  ${hex2}  ${ascii.join("")}`);
    }
    return lines.join("\n");
}

function _hexClass(b) {
    if (b === 0) return "hex-b-null";
    if (printableChar(b)) return "hex-b-print";
    return "hex-b-ctrl";
}

function _span(cls, text) {
    const el = document.createElement("span");
    el.className = cls;
    el.textContent = text;
    return el;
}

function _text(t) {
    return document.createTextNode(t);
}

function _buildRow(offset, row) {
    const div = document.createElement("div");
    div.className = "hex-row";

    div.appendChild(_span("hex-off", hex(offset, 4)));
    div.appendChild(_text("  "));

    // two groups of 8 separated by an extra space
    for (let i = 0; i < BYTES_PER_ROW; i++) {
        if (i === 8) div.appendChild(_text(" "));
        if (i < row.length) {
            div.appendChild(_span(_hexClass(row[i]), hex(row[i])));
        } else {
            div.appendChild(_span("hex-b-pad", "  "));
        }
        if (i < BYTES_PER_ROW - 1) div.appendChild(_text(" "));
    }

    div.appendChild(_text("  "));

    for (let i = 0; i < row.length; i++) {
        const b = row[i];
        const ch = printableChar(b);
        div.appendChild(ch ? _span("hex-a-print", ch) : _span("hex-a-dot", "."));
    }

    return div;
}

/**
 * Mount a highlighted hex view into container, replacing any existing content.
 * @param {Element} container
 * @param {Uint8Array} bytes
 */
export function mountHexView(container, bytes) {
    container.innerHTML = "";

    const info = document.createElement("div");
    info.className = "hex-info";
    info.textContent = `${bytes.length} byte${bytes.length !== 1 ? "s" : ""}`;

    const body = document.createElement("div");
    body.className = "hex-pre";

    if (!bytes.length) {
        const empty = document.createElement("div");
        empty.className = "hex-row hex-empty";
        empty.textContent = "(empty)";
        body.appendChild(empty);
    }
    for (let offset = 0; offset < bytes.length; offset += BYTES_PER_ROW) {
        body.appendChild(_buildRow(offset, bytes.subarray(offset, offset + BYTES_PER_ROW)));
    }

    container.appendChild(info);
    container.appendChild(body);
}
