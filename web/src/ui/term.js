/**
 * Terminal block: xterm.js UART-style I/O (TX port 252, RX port 254).
 * Toggled via btn-term in navbar; shares position with blk-disp.
 */

import { cpu, IO_TX_DATA, IO_TX_STATUS, IO_RX_DATA, IO_RX_STATUS } from "../state.js";

const elBlock = document.getElementById("blk-term");
const elToggle = document.getElementById("btn-term");
const elBody = document.getElementById("term-body");

let _xterm = null; // xterm.js Terminal instance
let _fitAddon = null; // xterm-addon-fit instance
let _onLayout = null; // callback → adjustBlockPositions
const _lineBuf = []; // current input line being edited
let _needsPrompt = false; // true when prompt should appear on next terminal open
let _pendingPrompt = false; // true after Enter; cleared when CPU goes silent for a batch
let _txThisFrame = false; // true if CPU emitted TX during the current batch
let _inInputMode = false; // true after user echo; cleared on device TX or Enter/Ctrl+C

// ── State ─────────────────────────────────────────────────────

const term = {
    visible: false,
    rxFifo: [], // pending input bytes from keyboard
    rxStaged: false, // true when a byte is staged in IO_RX_DATA
};

// ── xterm.js theme ────────────────────────────────────────────

function _xtermTheme(isDark) {
    return isDark
        ? {
              background: "#0d1117",
              foreground: "#39d353",
              cursor: "#39d353",
              selectionBackground: "#264f78",
          }
        : {
              background: "#f6f8fa",
              foreground: "#1a7f37",
              cursor: "#1a7f37",
              selectionBackground: "#add6ff",
          };
}

// ── Visibility ────────────────────────────────────────────────

function _applyVisible() {
    elBlock.style.display = term.visible ? "" : "none";
    elToggle.style.color = term.visible ? "var(--a-green)" : "var(--t-dim)";
    cpu.mem.set(IO_TX_STATUS, term.visible ? 1 : 0);

    const dispEl = document.getElementById("blk-disp");
    if (dispEl) dispEl.style.display = term.visible ? "none" : "";
}

function _toggle() {
    term.visible = !term.visible;
    localStorage.setItem("sim8-term", term.visible ? "on" : "off");
    _applyVisible();

    if (term.visible && _xterm) {
        _xterm.focus();
        if (_needsPrompt) _showPrompt();
    }
    _onLayout?.();
}

// ── TX/RX step-level polling (called from sim.js) ─────────────

/**
 * Pre-step: stage next RX byte if one is available and not yet staged.
 * Call before cpu.step().
 */
export function termPreStep() {
    if (!term.visible) return;
    if (!term.rxStaged && term.rxFifo.length > 0) {
        cpu.mem.set(IO_RX_DATA, term.rxFifo[0]);
        cpu.mem.set(IO_RX_STATUS, 1);
        term.rxStaged = true;
    }
}

/**
 * Post-step: emit TX byte if written; advance RX FIFO if byte was consumed.
 * Call after cpu.step(). Returns true if TX was emitted (for wire flash).
 */
export function termPostStep() {
    if (!term.visible) return false;
    let txEmitted = false;

    const tx = cpu.mem.get(IO_TX_DATA);
    if (tx !== 0) {
        if (_xterm) {
            // Only prepend reset sequence when transitioning from user-echo dim style
            const prefix = _inInputMode ? _ESC_RESET : "";
            _inInputMode = false;
            _xterm.write(prefix + String.fromCharCode(tx));
        }
        cpu.mem.set(IO_TX_DATA, 0);
        txEmitted = true;
        _txThisFrame = true;
    }

    // Program signals consumption by writing 0 to IO_RX_DATA
    if (term.rxStaged && cpu.mem.get(IO_RX_DATA) === 0) {
        term.rxFifo.shift();
        term.rxStaged = false;
        cpu.mem.set(IO_RX_STATUS, term.rxFifo.length > 0 ? 1 : 0);
    }

    return txEmitted;
}

/**
 * End-of-batch: show prompt once CPU goes silent after an Enter.
 * Call once per tick, after the full batch of cpu.step() calls.
 */
export function termEndFrame() {
    if (_pendingPrompt && !_txThisFrame) {
        _pendingPrompt = false;
        _showPrompt();
    }
    _txThisFrame = false;
}

// ── Prompt & colors ───────────────────────────────────────────

// ANSI: dim for user echo, reset for device output
const _ESC_INPUT = "\x1b[2m"; // dim  — user typed chars
const _ESC_RESET = "\x1b[0m"; // reset — device output uses default (theme fg)
const _PROMPT = "❯ ";

function _showPrompt() {
    if (_xterm) _xterm.write(_PROMPT);
    _needsPrompt = false;
}

// ── Line discipline ───────────────────────────────────────────

/**
 * Canonical mode: echo + line editing. Pushes completed lines to rxFifo.
 * Handles: printable chars (echo + buffer), Enter (flush line),
 * Backspace (erase last char), Ctrl+C (cancel line), escape sequences (ignored).
 */
function _lineDiscipline(data) {
    for (let i = 0; i < data.length; i++) {
        const ch = data[i];
        const code = data.charCodeAt(i);

        // Skip ANSI escape sequences (\x1b[ ... final-byte)
        if (ch === "\x1b") {
            i++;
            if (i < data.length && (data[i] === "[" || data[i] === "O")) {
                i++;
                while (i < data.length && !(data.charCodeAt(i) >= 0x40 && data.charCodeAt(i) <= 0x7e)) i++;
            }
            continue;
        }

        if (ch === "\r" || ch === "\n") {
            for (const b of _lineBuf) term.rxFifo.push(b);
            term.rxFifo.push(10); // LF
            _lineBuf.length = 0;
            _inInputMode = false;
            if (_xterm) _xterm.write(_ESC_RESET + "\r\n");
            _pendingPrompt = true; // deferred: show after CPU goes silent for a batch
            continue;
        }

        if (ch === "\x7f" || ch === "\x08") {
            if (_lineBuf.length > 0) {
                _lineBuf.pop();
                if (_xterm) _xterm.write("\b \b");
            }
            continue;
        }

        if (ch === "\x03") {
            _lineBuf.length = 0;
            _inInputMode = false;
            if (_xterm) _xterm.write(_ESC_RESET + "^C\r\n");
            _showPrompt(); // immediate — Ctrl+C won't trigger device output
            continue;
        }

        if (code >= 32 && code < 127) {
            _lineBuf.push(code);
            if (_xterm) {
                _xterm.write(_ESC_INPUT + ch);
                _inInputMode = true;
            }
        }
    }
}

// ── Reset ─────────────────────────────────────────────────────

export function resetTerm({ clearScreen = true } = {}) {
    term.rxFifo.length = 0;
    term.rxStaged = false;
    _lineBuf.length = 0;
    _pendingPrompt = false;
    _txThisFrame = false;
    _inInputMode = false;
    cpu.mem.set(IO_RX_DATA, 0);
    cpu.mem.set(IO_RX_STATUS, 0);
    cpu.mem.set(IO_TX_DATA, 0);
    cpu.mem.set(IO_TX_STATUS, term.visible ? 1 : 0);
    if (clearScreen && _xterm) {
        _xterm.clear();
        if (term.visible) _showPrompt();
        else _needsPrompt = true; // show on next open
    }
}

// ── Theme sync ────────────────────────────────────────────────

export function applyTermTheme(isDark) {
    if (_xterm) _xterm.options.theme = _xtermTheme(isDark);
}

export function isTermActive() {
    return term.visible;
}

export function fitTerm() {
    if (_fitAddon && term.visible) _fitAddon.fit();
}

// ── Init ──────────────────────────────────────────────────────

export function initTerm(onLayout, isDark) {
    _onLayout = onLayout;

    term.visible = localStorage.getItem("sim8-term") === "on";
    _applyVisible();

    // xterm.js and FitAddon are loaded from CDN as globals
    /* eslint-disable no-undef */
    _xterm = new Terminal({
        rows: 12,
        fontFamily: '"JetBrains Mono", monospace',
        fontSize: 11,
        theme: _xtermTheme(isDark),
        cursorBlink: true,
        scrollback: 500,
        convertEol: true,
    });
    _fitAddon = new FitAddon.FitAddon();
    /* eslint-enable no-undef */
    _xterm.loadAddon(_fitAddon);
    _xterm.open(elBody);

    // Keyboard input → line discipline → RX FIFO
    _xterm.onData(_lineDiscipline);

    elToggle.addEventListener("click", _toggle);
}
