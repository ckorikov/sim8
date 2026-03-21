/**
 * Multi-file tab management for the sim8 editor.
 */

import {
    getEditorSource,
    setEditorSource,
    clearExecLine,
    focusEditor,
    syncBpFromStore,
    setOnBpToggle,
} from "./editor.js";
import { breakpoints, MAIN_FILE } from "./breakpoints.js";
import { mountHexView } from "./hexview.js";

// Track mouse position so renderTabBar can detect hover on freshly inserted elements.
// (matches(':hover') returns false on newly inserted DOM nodes until the mouse moves.)
let _mouseX = -1;
let _mouseY = -1;

const DEFAULT_MAIN = `; Simple example
; Writes Hello World to the output

        JMP start
hello:
        DB "Hello World!"    ; Variable
        DB 0                 ; String terminator

start:
        MOV C, hello         ; Point to var
        MOV D, 232           ; Point to output
        CALL print
        HLT                  ; Stop execution

print:                       ; print(C:*from, D:*to)
        PUSH A
        PUSH B
        MOV B, 0

.loop:
        MOV A, [C]           ; Get char from var
        MOV [D], A           ; Write to output
        INC C
        INC D
        CMP B, [C]           ; Check if end
        JNZ .loop            ; jump if not

        POP B
        POP A
        RET

`;

/**
 * @typedef {{ type: 'text', content: string } | { type: 'binary', content: Uint8Array }} FileEntry
 */

/** @type {Map<string, FileEntry>} */
let files = new Map();

/** @type {string} */
let activeFile = MAIN_FILE;

/** @type {HTMLElement|null} */
let _editorCont = null;
/** @type {HTMLElement|null} */
let _hexCont = null;

// ── Binary detection ─────────────────────────────────────────────

const BINARY_EXTS = /\.(bin|rom|img|o|out|elf|exe|dat)$/i;

/**
 * @param {string} name
 * @param {ArrayBuffer} buffer
 * @returns {boolean}
 */
export function _isBinary(name, buffer) {
    if (BINARY_EXTS.test(name)) return true;
    const view = new Uint8Array(buffer, 0, Math.min(buffer.byteLength, 1024));
    for (const b of view) {
        if (b === 0) return true;
    }
    return false;
}

// ── View toggling ────────────────────────────────────────────────

function _showEditorView(text) {
    if (_editorCont) _editorCont.style.display = "";
    if (_hexCont) _hexCont.style.display = "none";
    setEditorSource(text);
}

function _showHexView(bytes) {
    if (_editorCont) _editorCont.style.display = "none";
    if (_hexCont) {
        _hexCont.style.display = "flex";
        mountHexView(_hexCont, bytes);
    }
}

function _activateEntry(name, entry) {
    if (entry?.type === "binary") {
        _showHexView(entry.content);
    } else {
        _showEditorView(entry?.content ?? "");
        syncBpFromStore(breakpoints.getForFile(name));
        focusEditor();
    }
}

// ── Name generation ──────────────────────────────────────────────

function generateDefaultName() {
    let n = 1;
    while (files.has(`New File ${n}.asm`)) n++;
    return `New File ${n}.asm`;
}

// ── Inline rename ────────────────────────────────────────────────

function _discardNewTab(name) {
    files.delete(name);
    if (activeFile === name) {
        activeFile = MAIN_FILE;
        const entry = files.get(MAIN_FILE);
        setEditorSource(entry?.type === "text" ? entry.content : "");
    }
}

function _commitRename(oldName, newName, isNew) {
    const trimmed = newName.trim();
    if (!trimmed || trimmed === oldName) {
        if (isNew && !trimmed) _discardNewTab(oldName);
        renderTabBar();
        focusEditor();
        return;
    }
    if (files.has(trimmed)) {
        renderTabBar(); // revert — name taken
        focusEditor();
        return;
    }
    // Rebuild map to preserve insertion order
    const updated = new Map();
    for (const [k, v] of files) {
        updated.set(k === oldName ? trimmed : k, v);
    }
    files = updated;
    breakpoints.renameFile(oldName, trimmed);
    if (activeFile === oldName) activeFile = trimmed;
    renderTabBar();
    focusEditor();
}

function _startRename(name, isNew = false) {
    const bar = document.getElementById("tab-bar");
    if (!bar) return;
    const btn = bar.querySelector(`.tab-btn[data-file="${CSS.escape(name)}"]`);
    if (!btn) return;

    const input = document.createElement("input");
    input.type = "text";
    input.className = "tab-name-input";
    input.value = name;

    let committed = false;
    const commit = () => {
        if (committed) return;
        committed = true;
        _commitRename(name, input.value, isNew);
    };

    input.addEventListener("keydown", (e) => {
        if (e.key === "Enter") {
            e.preventDefault();
            commit();
        } else if (e.key === "Escape") {
            committed = true;
            if (isNew) _discardNewTab(name);
            renderTabBar();
            focusEditor();
        }
    });
    input.addEventListener("blur", commit);

    btn.textContent = "";
    btn.appendChild(input);
    setTimeout(() => {
        input.focus();
        input.select();
    }, 0);
}

// ── Tab bar rendering ────────────────────────────────────────────

function renderTabBar() {
    const bar = document.getElementById("tab-bar");
    if (!bar) return;
    bar.innerHTML = "";

    const tabBtns = [];
    for (const name of files.keys()) {
        const btn = document.createElement("button");
        btn.className = "tab-btn" + (name === activeFile ? " active" : "");
        btn.dataset.file = name;
        btn.textContent = name;

        if (name !== MAIN_FILE) {
            const close = document.createElement("span");
            close.className = "tab-close";
            close.textContent = "\u00D7";
            close.addEventListener("click", (e) => {
                e.stopPropagation();
                closeTab(name);
            });
            btn.appendChild(close);

            btn.addEventListener("dblclick", (e) => {
                e.stopPropagation();
                _startRename(name, false);
            });
        }

        btn.addEventListener("mouseenter", () => btn.classList.add("is-hovered"));
        btn.addEventListener("mouseleave", () => btn.classList.remove("is-hovered"));
        btn.addEventListener("click", () => switchTab(name));
        bar.appendChild(btn);
        tabBtns.push(btn);
    }

    const addBtn = document.createElement("button");
    addBtn.className = "tab-add";
    addBtn.title = "New file";
    addBtn.textContent = "+";
    addBtn.addEventListener("click", () => addTab());
    bar.appendChild(addBtn);

    // elementFromPoint forces a layout reflow — call once after the full bar is built
    // so the cursor position is checked against the final layout (including the + button).
    if (_mouseX >= 0) {
        const under = document.elementFromPoint(_mouseX, _mouseY);
        for (const btn of tabBtns) {
            if (btn.contains(under)) {
                btn.classList.add("is-hovered");
                break;
            }
        }
    }
}

// ── Public API ───────────────────────────────────────────────────

export function saveCurrentTab() {
    const entry = files.get(activeFile);
    if (!entry || entry.type !== "text") return;
    files.set(activeFile, { type: "text", content: getEditorSource() });
}

function switchTab(name) {
    if (!files.has(name)) return;
    saveCurrentTab();
    activeFile = name;
    clearExecLine();
    _activateEntry(name, files.get(name));
    renderTabBar();
}

function addTab() {
    const name = generateDefaultName();
    files.set(name, { type: "text", content: "" });
    switchTab(name);
    _startRename(name, true);
}

function closeTab(name) {
    if (name === MAIN_FILE) return;
    const keys = [...files.keys()];
    const idx = keys.indexOf(name);
    files.delete(name);
    breakpoints.clearFile(name);
    if (activeFile === name) {
        const adjacent = keys[idx - 1] ?? keys[idx + 1] ?? MAIN_FILE;
        activeFile = adjacent;
        clearExecLine();
        _activateEntry(activeFile, files.get(activeFile));
    }
    renderTabBar();
}

/** Switch to a tab to follow execution — saves content but doesn't steal focus. */
export function switchTabForExec(filename) {
    const target = filename ?? MAIN_FILE;
    if (!files.has(target) || activeFile === target) return;
    const entry = files.get(target);
    if (entry?.type !== "text") return; // binary tabs can't be exec targets
    saveCurrentTab();
    activeFile = target;
    setEditorSource(entry.content);
    syncBpFromStore(breakpoints.getForFile(target));
    renderTabBar();
}

export function getVirtualFiles() {
    /** @type {Record<string, string | Uint8Array>} */
    const out = {};
    for (const [name, entry] of files.entries()) {
        if (name === MAIN_FILE) continue;
        out[name] = entry.type === "binary" ? entry.content : entry.content;
    }
    return out;
}

export function getMainSource() {
    const entry = files.get(MAIN_FILE);
    return entry?.type === "text" ? entry.content : "";
}

function _addFileTab(name, entry) {
    let tabName = name;
    if (files.has(tabName)) {
        const dot = tabName.lastIndexOf(".");
        const base = dot > 0 ? tabName.slice(0, dot) : tabName;
        const ext = dot > 0 ? tabName.slice(dot) : "";
        let n = 2;
        while (files.has(`${base} (${n})${ext}`)) n++;
        tabName = `${base} (${n})${ext}`;
    }
    files.set(tabName, entry);
    switchTab(tabName);
}

function _initDragDrop() {
    const bar = document.getElementById("tab-bar");
    const edCont = document.getElementById("editor-container");

    async function handleDrop(e) {
        e.preventDefault();
        bar?.classList.remove("drag-over");
        edCont?.classList.remove("drag-over");
        const droppedFiles = e.dataTransfer.files;
        if (!droppedFiles.length) return;
        saveCurrentTab();
        for (const file of droppedFiles) {
            const buffer = await file.arrayBuffer();
            if (_isBinary(file.name, buffer)) {
                _addFileTab(file.name, { type: "binary", content: new Uint8Array(buffer) });
            } else {
                const text = new TextDecoder().decode(buffer);
                _addFileTab(file.name, { type: "text", content: text });
            }
        }
    }

    for (const el of [bar, edCont].filter(Boolean)) {
        el.addEventListener("dragover", (e) => {
            e.preventDefault();
            e.dataTransfer.dropEffect = "copy";
            el.classList.add("drag-over");
        });
        el.addEventListener("dragleave", (e) => {
            if (!el.contains(e.relatedTarget)) {
                el.classList.remove("drag-over");
            }
        });
        el.addEventListener("drop", handleDrop);
    }
}

export function initTabs() {
    document.addEventListener(
        "mousemove",
        (e) => {
            _mouseX = e.clientX;
            _mouseY = e.clientY;
        },
        { passive: true },
    );
    files = new Map([[MAIN_FILE, { type: "text", content: DEFAULT_MAIN }]]);
    activeFile = MAIN_FILE;
    breakpoints.clearAll();
    setEditorSource(DEFAULT_MAIN);
    setOnBpToggle((line) => {
        breakpoints.toggle(activeFile, line);
        syncBpFromStore(breakpoints.getForFile(activeFile));
    });
    _editorCont = document.getElementById("editor-container");
    _hexCont = document.getElementById("hex-container");
    renderTabBar();
    _initDragDrop();
}
