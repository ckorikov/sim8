/**
 * CodeMirror editor: initialization, syntax highlighting, execution line marking.
 */

import {
    MNEMONICS,
    MNEMONICS_FP,
    MNEMONICS_VU,
    Reg,
    FP_REGISTERS,
    ISA,
    ISA_FP,
    ISA_VU,
    MNEMONIC_ALIASES,
    FP_CONTROL_MNEMONICS,
} from "../lib/isa.js";
import {
    MNEMONIC_INFO,
    MNEMONIC_FLAGS,
    MNEMONIC_FP_EXCEPTIONS,
    MNEMONIC_NOTES,
    MNEMONIC_FORMS_OVERRIDE,
    SIG_LABELS,
    FP_FMT_NAMES,
    FP_FORMAT_DOCS,
    REGISTER_DOCS,
    DIRECTIVE_DOCS,
} from "../lib/isa-docs.js";

const _ALL_MNEMONICS = [...MNEMONICS, ...MNEMONICS_FP, ...Object.keys(MNEMONIC_ALIASES), ...MNEMONICS_VU];
const ALL_MNEMONICS_RE = new RegExp("\\b(" + _ALL_MNEMONICS.join("|") + ")(\\.[A-Z0-9]+)*\\b", "i");
const ALL_REGISTERS_RE = new RegExp(
    "\\b(" + [...Object.keys(Reg), ...Object.keys(FP_REGISTERS), "VA", "VB", "VC", "VM", "VL"].join("|") + ")\\b",
    "i",
);

let cmView = null;
let cmExecEffect = null;
let cmSetDiagnostics = null;
let cmScrollIntoView = null;
let cmSetBps = null;
let _onBpToggle = null;

/** Register a callback invoked when the user clicks the BP gutter: fn(lineNo: number). */
export function setOnBpToggle(fn) {
    _onBpToggle = fn;
}

/**
 * Load a Set<lineNo> into the editor's BP gutter (mirrors the global store for the
 * currently active file). Call this after switching tabs or clearing breakpoints.
 * @param {Set<number>} set
 */
export function syncBpFromStore(set) {
    if (!cmView || !cmSetBps) return;
    cmView.dispatch({ effects: cmSetBps.of(set) });
}

export function highlightExecLine(line) {
    if (!cmView || !cmExecEffect) return;
    cmView.dispatch({ effects: cmExecEffect.of(line) });
    if (cmScrollIntoView && line >= 1 && line <= cmView.state.doc.lines) {
        const pos = cmView.state.doc.line(line).from;
        cmView.dispatch({ effects: cmScrollIntoView(pos, { y: "center" }) });
    }
}

export function getEditorSource() {
    return cmView ? cmView.state.doc.toString() : document.querySelector("#editor-container textarea")?.value || "";
}

export function setEditorSource(text) {
    if (!cmView) return;
    // Clear the exec-line in the same transaction as the doc change so the
    // stale decoration never gets mapped (and potentially misplaced) in the
    // new document before highlightExecLine() fires.
    const effects = cmExecEffect ? [cmExecEffect.of(0)] : [];
    cmView.dispatch({
        changes: { from: 0, to: cmView.state.doc.length, insert: text },
        effects,
    });
}

export function clearExecLine() {
    if (!cmView || !cmExecEffect) return;
    cmView.dispatch({ effects: cmExecEffect.of(0) });
}

export function showDiagnostic(line, message) {
    if (!cmView || !cmSetDiagnostics) return;
    const doc = cmView.state.doc;
    if (line < 1 || line > doc.lines) return;
    const lineObj = doc.line(line);
    cmView.dispatch(
        cmSetDiagnostics(cmView.state, [{ from: lineObj.from, to: lineObj.to, severity: "error", message }]),
    );
    if (cmScrollIntoView) {
        cmView.dispatch({ effects: cmScrollIntoView(lineObj.from, { y: "center" }) });
    }
}

export function clearDiagnostics() {
    if (!cmView || !cmSetDiagnostics) return;
    cmView.dispatch(cmSetDiagnostics(cmView.state, []));
}

export function focusEditor() {
    if (!cmView) return;
    cmView.focus();
}

export async function initEditor(container, defaultCode) {
    try {
        const [
            { EditorView, basicSetup },
            { EditorState, StateEffect, StateField },
            { Decoration, GutterMarker, gutter, keymap },
            { StreamLanguage, HighlightStyle, syntaxHighlighting },
            { tags },
            { autocompletion },
            { toggleComment, indentWithTab },
            { setDiagnostics },
        ] = await Promise.all([
            import("https://esm.sh/codemirror"),
            import("https://esm.sh/@codemirror/state"),
            import("https://esm.sh/@codemirror/view"),
            import("https://esm.sh/@codemirror/language"),
            import("https://esm.sh/@lezer/highlight"),
            import("https://esm.sh/@codemirror/autocomplete"),
            import("https://esm.sh/@codemirror/commands"),
            import("https://esm.sh/@codemirror/lint"),
        ]);

        cmSetDiagnostics = setDiagnostics;

        const setExecLine = StateEffect.define();
        cmExecEffect = setExecLine;
        const execLineDeco = Decoration.line({ class: "cm-exec-line" });

        class ExecMarker extends GutterMarker {
            toDOM() {
                const el = document.createElement("span");
                el.textContent = "\u25B6";
                el.className = "cm-exec-arrow";
                return el;
            }
        }
        const execMarker = new ExecMarker();

        const execLineField = StateField.define({
            create() {
                return { line: -1, decos: Decoration.none };
            },
            update(state, tr) {
                for (const e of tr.effects) {
                    if (e.is(setExecLine)) {
                        if (e.value < 1) return { line: -1, decos: Decoration.none };
                        const doc = tr.state.doc;
                        if (e.value > doc.lines) return { line: -1, decos: Decoration.none };
                        const lineStart = doc.line(e.value).from;
                        return {
                            line: e.value,
                            decos: Decoration.set([execLineDeco.range(lineStart)]),
                        };
                    }
                }
                // When the document changes, old positions are stale — clear the decoration
                // to avoid applying it to a document it no longer matches.
                if (tr.docChanged) return { line: -1, decos: Decoration.none };
                return state;
            },
        });
        const execDecoExt = EditorView.decorations.from(execLineField, (s) => s.decos);

        const asmLang = StreamLanguage.define({
            token(s) {
                if (s.match(/;.*/)) return "comment";
                if (s.match(/@(?:include|page)\b/i)) return "moduleKeyword";
                if (s.match(ALL_MNEMONICS_RE)) return "keyword";
                if (s.match(ALL_REGISTERS_RE)) return "variableName";
                if (s.match(/\b0x[0-9A-Fa-f]+\b/)) return "number";
                if (s.match(/\b[0-9]+(\.[0-9]+)?\b/)) return "number";
                if (s.match(/'[^']*'/) || s.match(/"[^"]*"/)) return "string";
                if (s.match(/\[.*?\]/)) return "bracket";
                if (s.match(/\.?\w+:/)) return "labelName";
                s.next();
                return null;
            },
            languageData: { commentTokens: { line: ";" } },
        });

        const sim8Theme = EditorView.theme(
            {
                "&": { height: "100%", background: "var(--t-canvas)", color: "var(--t-mid)" },
                ".cm-scroller": { fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", lineHeight: "1.6" },
                ".cm-gutters": {
                    background: "var(--t-nav)",
                    borderRight: "1px solid var(--t-border)",
                    color: "var(--t-dim)",
                    minWidth: "36px",
                },
                ".cm-gutter": { fontSize: "11px" },
                ".cm-activeLine": { background: "rgba(204,85,0,0.04)" },
                ".cm-activeLineGutter": { background: "rgba(204,85,0,0.06)", color: "var(--t-dim)" },
                ".cm-cursor": { borderLeftColor: "var(--a-orange)", borderLeftWidth: "1.5px" },
                ".cm-selectionBackground": { background: "var(--a-orange-a20) !important" },
                ".cm-matchingBracket": { background: "var(--a-orange-a20)", color: "var(--a-orange) !important" },
                ".cm-searchMatch": { background: "var(--a-orange-a20)" },
                ".cm-foldPlaceholder": {
                    background: "var(--t-surface)",
                    border: "1px solid var(--t-border)",
                    color: "var(--t-dim)",
                },
                ".cm-tooltip": {
                    background: "var(--t-surface)",
                    border: "1px solid var(--t-border)",
                    color: "var(--t-text)",
                },
                ".cm-panels": {
                    background: "var(--t-nav)",
                    borderTop: "1px solid var(--t-border)",
                    color: "var(--t-mid)",
                },
            },
            { dark: true },
        );

        const sim8Highlight = HighlightStyle.define([
            { tag: tags.keyword, class: "cm-hl-kw" },
            { tag: tags.moduleKeyword, class: "cm-hl-directive" },
            { tag: tags.variableName, class: "cm-hl-var" },
            { tag: tags.number, class: "cm-hl-num" },
            { tag: tags.string, class: "cm-hl-str" },
            { tag: tags.comment, class: "cm-hl-cmt" },
            { tag: tags.bracket, class: "cm-hl-brk" },
            { tag: tags.labelName, class: "cm-hl-lbl" },
        ]);

        const setBps = StateEffect.define();
        cmSetBps = setBps;

        const bpField = StateField.define({
            create() {
                return new Set();
            },
            update(bps, tr) {
                for (const e of tr.effects) {
                    if (e.is(setBps)) return new Set(e.value);
                }
                return bps;
            },
        });

        class BpMarker extends GutterMarker {
            constructor(active = false) {
                super();
                this.active = active;
            }
            toDOM() {
                const el = document.createElement("span");
                el.textContent = "●";
                el.className = this.active ? "cm-bp-marker cm-bp-active" : "cm-bp-marker";
                return el;
            }
            eq(other) {
                return other.active === this.active;
            }
        }
        const bpMarker = new BpMarker(false);
        const bpMarkerActive = new BpMarker(true);
        const debugGutter = gutter({
            class: "cm-debug-gutter",
            lineMarker(view, line) {
                const lineNum = view.state.doc.lineAt(line.from).number;
                const bps = view.state.field(bpField);
                const execState = view.state.field(execLineField);
                const isExec = execState.line === lineNum;
                if (bps.has(lineNum)) return isExec ? bpMarkerActive : bpMarker;
                return isExec ? execMarker : null;
            },
            lineMarkerChange(update) {
                return (
                    update.startState.field(bpField) !== update.state.field(bpField) ||
                    update.startState.field(execLineField) !== update.state.field(execLineField)
                );
            },
            domEventHandlers: {
                click(view, line) {
                    _onBpToggle?.(view.state.doc.lineAt(line.from).number);
                    return true;
                },
            },
        });

        function buildMnemonicVariants() {
            const variants = {};
            for (const def of [...ISA, ...ISA_FP, ...ISA_VU]) {
                if (MNEMONIC_FORMS_OVERRIDE[def.mnemonic]) continue;
                const sig = def.sig.map((s) => SIG_LABELS[s] || "?").join(", ");
                const form = sig ? `${def.mnemonic} ${sig}` : def.mnemonic;
                if (!variants[def.mnemonic]) variants[def.mnemonic] = new Set();
                variants[def.mnemonic].add(form);
            }
            for (const [mn, forms] of Object.entries(MNEMONIC_FORMS_OVERRIDE)) {
                variants[mn] = new Set(forms);
            }
            return variants;
        }
        const MNEMONIC_VARIANTS = buildMnemonicVariants();

        function _infoline(parent, cls, text) {
            const d = document.createElement("div");
            d.className = cls;
            d.textContent = text;
            parent.appendChild(d);
        }

        function mnemonicInfoDom(mnemonic, aliasOf) {
            const el = document.createElement("div");
            el.className = "cm-instr-info";
            const canonical = aliasOf || mnemonic;
            _infoline(el, "cm-instr-desc", MNEMONIC_INFO[canonical] || canonical);
            if (aliasOf) _infoline(el, "cm-instr-form", `= ${aliasOf}`);
            const forms = MNEMONIC_VARIANTS[canonical];
            if (forms) {
                for (const f of forms) _infoline(el, "cm-instr-form", f);
            }
            const flags = MNEMONIC_FLAGS[canonical];
            if (flags) _infoline(el, "cm-instr-form", `Flags: ${flags}`);
            const fpex = MNEMONIC_FP_EXCEPTIONS[canonical];
            if (fpex) _infoline(el, "cm-instr-form", `FP exc: ${fpex}`);
            if (MNEMONICS_FP.has(canonical) && !FP_CONTROL_MNEMONICS.has(canonical)) {
                const suffixes = Object.entries(FP_FORMAT_DOCS)
                    .filter(([k]) => k.length <= 2)
                    .map(([k, v]) => `.${k}=${v.name}`)
                    .join(", ");
                _infoline(el, "cm-instr-form", `Formats: ${suffixes}`);
            }
            const note = MNEMONIC_NOTES[canonical];
            if (note) _infoline(el, "cm-instr-form", note);
            return el;
        }

        const MNEMONIC_COMPLETIONS = [
            ...[...MNEMONICS, ...MNEMONICS_FP, ...MNEMONICS_VU].map((m) => ({
                label: m,
                info: () => mnemonicInfoDom(m),
                type: "keyword",
            })),
            ...Object.entries(MNEMONIC_ALIASES).map(([alias, canonical]) => ({
                label: alias,
                detail: `= ${canonical}`,
                info: () => mnemonicInfoDom(alias, canonical),
                type: "keyword",
            })),
        ];

        const REGISTER_COMPLETIONS = [
            ...Object.keys(Reg).map((r) => {
                const doc = REGISTER_DOCS[r];
                return { label: r, info: doc ? doc.description : r, type: "variable" };
            }),
            ...Object.keys(FP_REGISTERS).map((r) => {
                const doc = REGISTER_DOCS[r];
                const fmt = FP_FMT_NAMES[FP_REGISTERS[r].fmt] || `${FP_REGISTERS[r].width}b`;
                return { label: r, info: doc ? doc.description : `FP ${fmt}`, type: "variable" };
            }),
            ...["VA", "VB", "VC", "VM", "VL"].map((r) => ({
                label: r,
                info: r === "VL" ? "VU vector length (16-bit)" : `VU address pointer (16-bit)`,
                type: "variable",
            })),
        ];

        function sim8CompletionSource(context) {
            const atWord = context.matchBefore(/@\w*/i);
            if (atWord && (atWord.from < atWord.to || context.explicit)) {
                return {
                    from: atWord.from,
                    options: [
                        {
                            label: "@include",
                            type: "keyword",
                            detail: '"filename.asm"',
                            info: DIRECTIVE_DOCS["@INCLUDE"]?.description,
                        },
                        {
                            label: "@page",
                            type: "keyword",
                            detail: "N[, offset]",
                            info: DIRECTIVE_DOCS["@PAGE"]?.description,
                        },
                    ],
                };
            }

            const word = context.matchBefore(/[\w.]+/);
            if (!word || (word.from === word.to && !context.explicit)) return null;

            const prefix = word.text.toUpperCase();
            const line = context.state.doc.lineAt(word.from);
            const beforeWord = line.text.slice(0, word.from - line.from);
            if (beforeWord.includes(";")) return null;
            const isMnemonicPos = /^\s*(\w+\s*:)?\s*$/.test(beforeWord);

            if (isMnemonicPos) {
                const options = MNEMONIC_COMPLETIONS.filter((o) => o.label.startsWith(prefix));
                return options.length ? { from: word.from, options } : null;
            }

            const options = REGISTER_COMPLETIONS.filter((o) => o.label.startsWith(prefix));
            const seen = new Set(options.map((o) => o.label.toUpperCase()));
            const labelRe = /^[ \t]*(\w+)\s*:/gm;
            let m;
            const docText = context.state.doc.toString();
            while ((m = labelRe.exec(docText)) !== null) {
                if (!seen.has(m[1].toUpperCase()) && m[1].toUpperCase().startsWith(prefix)) {
                    options.push({ label: m[1], type: "namespace", info: "Label" });
                    seen.add(m[1].toUpperCase());
                }
            }
            return options.length ? { from: word.from, options } : null;
        }

        cmScrollIntoView = EditorView.scrollIntoView;
        cmView = new EditorView({
            state: EditorState.create({
                doc: defaultCode,
                extensions: [
                    basicSetup,
                    asmLang,
                    sim8Theme,
                    syntaxHighlighting(sim8Highlight),
                    execLineField,
                    execDecoExt,
                    bpField,
                    debugGutter,
                    autocompletion({ override: [sim8CompletionSource] }),
                    keymap.of([{ key: "Mod-/", run: toggleComment }, indentWithTab]),
                ],
            }),
            parent: container,
        });
    } catch (e) {
        console.warn("CodeMirror failed to load, using textarea fallback:", e);
        const ta = document.createElement("textarea");
        ta.style.cssText =
            "width:100%;height:100%;background:var(--t-canvas);color:var(--t-text);padding:16px;resize:none;outline:none;border:none;font-family:'JetBrains Mono',monospace;font-size:13px;tab-size:4;";
        ta.value = defaultCode;
        ta.spellcheck = false;
        container.appendChild(ta);
    }
}
