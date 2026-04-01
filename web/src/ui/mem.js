/**
 * Memory block renderer: 16x16 grid, page navigation, format toggle, instruction highlighting.
 */

import {
    cpu,
    colors,
    asm,
    hex,
    printableChar,
    escapeHtml,
    cssVar,
    initFormatToggle,
    STACK_BASE,
    IO_BASE,
    PAGE_SIZE,
} from "../state.js";
import { decodeFloat32, decodeFloat16, decodeBfloat16, decodeOfp8E4M3, decodeOfp8E5M2 } from "../../lib/fp.js";
import { BY_CODE, BY_CODE_FP, OpType, FP_REGISTERS, decodeRegaddr } from "../../lib/isa.js";
import { isHidden } from "./marker-toggle.js";

// ── Data inspector tooltip ───────────────────────────────────────

const tooltip = document.createElement("div");
tooltip.id = "mem-tooltip";
document.body.appendChild(tooltip);

const FPM_TO_NAME = Object.fromEntries(
    Object.entries(FP_REGISTERS).map(([name, { phys, pos, fmt }]) => [(phys << 6) | (pos << 3) | fmt, name]),
);
const REG_NAMES = ["A", "B", "C", "D", "SP", "DP"];

function disasmInstr(absAddr) {
    const b0 = cpu.mem.get(absAddr);
    const def = BY_CODE[b0] ?? BY_CODE_FP[b0];
    if (!def) return null;

    const bytes = readBytes(absAddr, def.size);
    const parts = [];
    let bi = 1;
    for (const ot of def.sig) {
        let op;
        if (ot === OpType.REG || ot === OpType.REG_ARITH || ot === OpType.REG_STACK || ot === OpType.REG_GPR) {
            op = REG_NAMES[bytes[bi]] ?? `r${bytes[bi]}`;
            bi++;
        } else if (ot === OpType.IMM) {
            op = String(bytes[bi]);
            bi++;
        } else if (ot === OpType.MEM) {
            op = `[${hex(bytes[bi], 2)}]`;
            bi++;
        } else if (ot === OpType.REGADDR) {
            const [rc, off] = decodeRegaddr(bytes[bi]);
            const rn = REG_NAMES[rc] ?? `r${rc}`;
            op = off === 0 ? `[${rn}]` : `[${rn}${off > 0 ? "+" : ""}${off}]`;
            bi++;
        } else if (ot === OpType.FP_REG) {
            op = FPM_TO_NAME[bytes[bi]] ?? `fpm(${hex(bytes[bi])})`;
            bi++;
        } else if (ot === OpType.FP_IMM8) {
            op = `0x${hex(bytes[bi])}`;
            bi++;
        } else if (ot === OpType.FP_IMM16) {
            op = `0x${hex(bytes[bi] | (bytes[bi + 1] << 8), 4)}`;
            bi += 2;
        }
        if (op !== undefined) parts.push(op);
    }
    return {
        text: def.mnemonic + (parts.length ? " " + parts.join(", ") : ""),
        size: def.size,
        cost: def.cost,
        formatDep: def.formatDep,
        confirmed: asm.instrStarts.has(absAddr),
    };
}

function readBytes(base, n) {
    return Array.from({ length: n }, (_, i) => cpu.mem.get((base + i) & 0xffff));
}

function fmtF(v, prec) {
    return isFinite(v) ? v.toPrecision(prec) : String(v);
}

function buildTooltip(absAddr) {
    const val = cpu.mem.get(absAddr);
    const i8 = val >= 128 ? val - 256 : val;
    const bin = val
        .toString(2)
        .padStart(8, "0")
        .replace(/(.{4})/, "$1 ");
    const ch = printableChar(val);

    const b4 = readBytes(absAddr, 4);
    const b2 = b4.slice(0, 2);
    const u16 = b2[0] | (b2[1] << 8);
    const i16 = u16 >= 0x8000 ? u16 - 0x10000 : u16;
    const u32 = (b4[0] | (b4[1] << 8) | (b4[2] << 16) | (b4[3] << 24)) >>> 0;
    const i32 = u32 | 0;

    const row = (l, v, d) =>
        `<div class="mtt-row"><span class="mtt-l">${l}</span>` +
        `<span class="mtt-v">${v}${d != null ? `<span class="mtt-d"> ${d}</span>` : ""}</span></div>`;
    const sep = `<div class="mtt-sep"></div>`;

    return (
        `<div class="mtt-hdr">[${hex(absAddr, 4)}] = ${hex(val)}${asm.labelNames.has(absAddr) ? `<span class="mtt-label"> ${escapeHtml(asm.labelNames.get(absAddr))}</span>` : ""}</div>` +
        row("u8", val) +
        row("i8", i8) +
        row("bin", bin) +
        (ch ? row("char", escapeHtml(`'${ch}'`)) : "") +
        sep +
        row("e4m3", fmtF(decodeOfp8E4M3(val), 3)) +
        row("e5m2", fmtF(decodeOfp8E5M2(val), 3)) +
        sep +
        row("u16le", hex(u16, 4), u16) +
        row("i16le", i16) +
        row("f16le", fmtF(decodeFloat16(b2), 4)) +
        row("bf16", fmtF(decodeBfloat16(b2), 4)) +
        sep +
        row("u32le", hex(u32, 8), u32) +
        row("i32le", i32) +
        row("f32le", fmtF(decodeFloat32(b4), 6)) +
        instrRow(absAddr, row, sep)
    );
}

function instrRow(absAddr, row, sep) {
    const instr = disasmInstr(absAddr);
    if (!instr) return "";
    const costStr = instr.formatDep ? `${instr.cost}+c` : `${instr.cost}c`;
    const tag = instr.confirmed ? "● asm" : "? asm";
    return sep + row(tag, escapeHtml(instr.text), `${instr.size}B ${costStr}`);
}

function posTooltip(x, y) {
    const tw = tooltip.offsetWidth;
    const th = tooltip.offsetHeight;
    const left = x + 14 + tw > window.innerWidth ? x - tw - 6 : x + 14;
    const top = y + 14 + th > window.innerHeight ? y - th - 6 : y + 14;
    tooltip.style.left = left + "px";
    tooltip.style.top = top + "px";
}

const memFmt = initFormatToggle("blk-mem", "#fmt-tabs", "fmt", () => renderMemory());
let page = 0;

function fmtByte(v) {
    return memFmt.get() === "dec" ? v.toString().padStart(3, " ") : hex(v);
}

function cellClass(addr, val, showInstr) {
    const pageBase = page * PAGE_SIZE;
    const absAddr = pageBase + addr;
    let cl = "mem-cell";

    if (showInstr && asm.instrStarts.has(absAddr)) {
        cl += " instr-start";
    } else if (page === 0 && addr >= IO_BASE) {
        cl += " io";
    } else if (page === 0 && addr >= STACK_BASE) {
        cl += " stack";
    } else if (showInstr && absAddr < asm.codeLen && val) {
        cl += " instr";
    }

    if (asm.labelAddrs.has(absAddr)) cl += " label";

    for (const m of _markers) {
        if (absAddr >= m.addr && absAddr < m.addr + m.len) {
            if (m.exclusive) return cl + m.cls;
            cl += m.cls;
        }
    }
    return cl;
}

/** Build pointer markers: [{addr, len, cls, exclusive}] for CPU and VU. */
function _buildMarkers() {
    const markers = [];
    const seen = new Set();

    function add(addr, len, cls, regName, exclusive = false) {
        if (isHidden(regName)) return;
        const key = `${addr}:${len}`;
        if (seen.has(key)) return;
        seen.add(key);
        markers.push({ addr, len, cls: " " + cls, exclusive });
    }

    // CPU instruction/stack pointers (exclusive — override other markers)
    add(cpu.ip, 1, "marker-ip", "IP", true);
    add(cpu.sp, 1, "marker-sp", "SP", true);

    // CPU scalar pointers
    const dpBase = cpu.dp * PAGE_SIZE;
    add(dpBase + cpu.a, 1, "marker-a", "A");
    add(dpBase + cpu.b, 1, "marker-b", "B");
    add(dpBase + cpu.c, 1, "marker-c", "C");
    add(dpBase + cpu.d, 1, "marker-d", "D");

    // VU pointer windows: fixed 16-byte memory port width
    const vu = cpu.vu;
    if (vu && vu.regs.vl > 0) {
        add(vu.regs.va, 16, "marker-va", "VA");
        add(vu.regs.vb, 16, "marker-vb", "VB");
        add(vu.regs.vc, 16, "marker-vc", "VC");
    }

    return markers;
}

let _markers = [];

export function renderMemory() {
    _markers = _buildMarkers();
    const showInstr = document.getElementById("chk-instr").checked;
    const baseCw = parseInt(cssVar("--s-mem-cell-w")) || 28;
    const cellW = memFmt.get() === "dec" ? baseCw + 2 : baseCw;
    const rowW = parseInt(cssVar("--s-mem-row-w")) || 24;
    const cellFont = parseInt(cssVar("--s-mem-cell-font")) || 10;
    const pageBase = page * PAGE_SIZE;

    const rows = [];
    const hdrs = Array.from(
        { length: 16 },
        (_, c) => `<div class="mh" style="width:${cellW}px">${hex(c, 1)}</div>`,
    ).join("");
    rows.push(`<div style="display:flex;"><div class="mr" style="width:${rowW}px"></div>${hdrs}</div>`);

    for (let r = 0; r < 16; r++) {
        const cells = Array.from({ length: 16 }, (_, c) => {
            const addr = r * 16 + c;
            const absAddr = pageBase + addr;
            const val = cpu.mem.get(absAddr);
            const lname = asm.labelNames.get(absAddr);
            const title = lname ? ` title="${escapeHtml(lname)}"` : "";
            return `<div class="${cellClass(addr, val, showInstr)}" style="width:${cellW}px;font-size:${cellFont}px" data-addr="${absAddr}"${title}>${fmtByte(val)}</div>`;
        }).join("");
        rows.push(
            `<div style="display:flex;"><div class="mr" style="width:${rowW}px">${hex(pageBase + r * 16, 4)}</div>${cells}</div>`,
        );
    }

    const legend = [
        [colors.mid, "data"],
        [colors.yl, "stack"],
        [colors.gr, "i/o"],
        [colors.or, "ip"],
        [colors.yl, "sp"],
        [colors.bl, "label"],
    ]
        .map(([c, l]) => `<span><b style="color:${c};">&#9632;</b> ${l}</span>`)
        .join("");

    document.getElementById("mem-grid").innerHTML =
        `<div style="line-height:0;display:inline-block;">${rows.join("")}</div>` +
        `<div style="margin-top:8px;display:flex;gap:12px;font-size:8px;color:${colors.dim};justify-content:center;">${legend}</div>`;
}

export function setPage(p) {
    page = p;
    document.getElementById("page-num").textContent = `${page}/255`;
    renderMemory();
}

document.getElementById("chk-instr").addEventListener("change", () => renderMemory());

// Page navigation
document.getElementById("page-prev").addEventListener("click", () => {
    if (page > 0) setPage(page - 1);
});
document.getElementById("page-next").addEventListener("click", () => {
    if (page < 255) setPage(page + 1);
});

// Data inspector tooltip
let ttCell = null;

document.getElementById("mem-grid").addEventListener("mouseover", (e) => {
    const cell = e.target.closest("[data-addr]");
    if (cell === ttCell) return;
    ttCell = cell;
    if (!cell) {
        tooltip.style.display = "none";
        return;
    }
    tooltip.innerHTML = buildTooltip(parseInt(cell.dataset.addr));
    tooltip.style.display = "block";
    posTooltip(e.clientX, e.clientY);
});
document.getElementById("mem-grid").addEventListener("mousemove", (e) => {
    if (ttCell) posTooltip(e.clientX, e.clientY);
});
document.getElementById("mem-grid").addEventListener("mouseleave", () => {
    ttCell = null;
    tooltip.style.display = "none";
});
