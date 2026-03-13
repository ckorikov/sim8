/**
 * CodeMirror editor: initialization, syntax highlighting, execution line marking.
 */

import { MNEMONICS, MNEMONICS_FP, REGISTERS, FP_REGISTERS, ISA, ISA_FP, OpType } from "../lib/isa.js";

const ALL_MNEMONICS_RE = new RegExp("\\b(" + [...MNEMONICS, ...MNEMONICS_FP].join("|") + ")\\b", "i");
const ALL_REGISTERS_RE = new RegExp(
    "\\b(" + [...Object.keys(REGISTERS), ...Object.keys(FP_REGISTERS)].join("|") + ")\\b",
    "i",
);

let cmView = null;
let cmExecEffect = null;
let cmScrollIntoView = null;
let cmBpField = null;

export function highlightExecLine(line) {
    if (!cmView || !cmExecEffect) return;
    cmView.dispatch({ effects: cmExecEffect.of(line) });
    if (cmScrollIntoView && line >= 1 && line <= cmView.state.doc.lines) {
        const pos = cmView.state.doc.line(line).from;
        cmView.dispatch({ effects: cmScrollIntoView(pos, { y: "center" }) });
    }
}

export function getBreakpoints() {
    if (!cmView || !cmBpField) return new Set();
    return cmView.state.field(cmBpField);
}

export function getEditorSource() {
    return cmView ? cmView.state.doc.toString() : document.querySelector("#editor-container textarea")?.value || "";
}

export async function initEditor(container, defaultCode) {
    try {
        const [
            { EditorView, basicSetup },
            { EditorState, StateEffect, StateField },
            { Decoration, GutterMarker, gutter },
            { StreamLanguage, HighlightStyle, syntaxHighlighting },
            { tags },
            { autocompletion },
        ] = await Promise.all([
            import("https://esm.sh/codemirror"),
            import("https://esm.sh/@codemirror/state"),
            import("https://esm.sh/@codemirror/view"),
            import("https://esm.sh/@codemirror/language"),
            import("https://esm.sh/@lezer/highlight"),
            import("https://esm.sh/@codemirror/autocomplete"),
        ]);

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
                return state;
            },
        });
        const execDecoExt = EditorView.decorations.from(execLineField, (s) => s.decos);

        const asmLang = StreamLanguage.define({
            token(s) {
                if (s.match(/;.*/)) return "comment";
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
            { tag: tags.variableName, class: "cm-hl-var" },
            { tag: tags.number, class: "cm-hl-num" },
            { tag: tags.string, class: "cm-hl-str" },
            { tag: tags.comment, class: "cm-hl-cmt" },
            { tag: tags.bracket, class: "cm-hl-brk" },
            { tag: tags.labelName, class: "cm-hl-lbl" },
        ]);

        const toggleBp = StateEffect.define();

        const bpField = StateField.define({
            create() {
                return new Set();
            },
            update(bps, tr) {
                for (const e of tr.effects) {
                    if (e.is(toggleBp)) {
                        const next = new Set(bps);
                        if (next.has(e.value)) next.delete(e.value);
                        else next.add(e.value);
                        return next;
                    }
                }
                return bps;
            },
        });
        cmBpField = bpField;

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
                    view.dispatch({ effects: toggleBp.of(view.state.doc.lineAt(line.from).number) });
                    return true;
                },
            },
        });

        const MNEMONIC_INFO = {
            HLT: "Halt CPU execution",
            MOV: "Copy value: reg, mem, or immediate",
            ADD: "dest = dest + src; sets C, Z",
            SUB: "dest = dest - src; sets C, Z",
            INC: "dest = dest + 1; sets C, Z",
            DEC: "dest = dest - 1; sets C, Z",
            CMP: "Compare (sets Z, C without storing)",
            MUL: "A = A * src; sets C, Z",
            DIV: "A = A / src (integer); FAULT if src=0",
            AND: "dest = dest & src; C=0, sets Z",
            OR: "dest = dest | src; C=0, sets Z",
            XOR: "dest = dest ^ src; C=0, sets Z",
            NOT: "dest = ~dest; C=0, sets Z",
            SHL: "dest = dest << n; sets C if overflow",
            SHR: "dest = dest >>> n; sets C if bits lost",
            JMP: "Unconditional jump",
            JZ: "Jump if Z=1 (equal)",
            JNZ: "Jump if Z=0 (not equal)",
            JC: "Jump if C=1 (borrow/underflow)",
            JNC: "Jump if C=0 (no borrow)",
            JA: "Jump if C=0 and Z=0 (unsigned greater)",
            JNA: "Jump if C=1 or Z=1 (unsigned <=)",
            PUSH: "Push to stack; SP--; FAULT if SP=0",
            POP: "Pop from stack; SP++; FAULT if SP>=231",
            CALL: "Push return addr, jump to target",
            RET: "Pop addr from stack, jump to it",
            DB: "Define raw byte(s) or ASCII string",
            FMOV: "FP load/store or register copy",
            FADD: "FP dst = dst + src",
            FSUB: "FP dst = dst - src",
            FMUL: "FP dst = dst * src",
            FDIV: "FP dst = dst / src",
            FCMP: "FP compare; sets Z, C (Z=C=1 if NaN)",
            FABS: "Clear sign bit of FP register",
            FNEG: "Toggle sign bit of FP register",
            FSQRT: "FP square root",
            FCVT: "Convert between FP formats",
            FITOF: "uint8 GPR to FP register",
            FFTOI: "FP to uint8 GPR (saturating)",
            FSTAT: "Read FPSR (exception flags) to GPR",
            FCFG: "Read FPCR (rounding mode) to GPR",
            FSCFG: "Write GPR to FPCR (bits [1:0] only)",
            FCLR: "Clear all FPSR sticky flags",
            FCLASS: "Classify FP value to 8-bit bitmask",
            FMADD: "FP dst = src * mem + dst (fused)",
        };
        const SIG_LABELS = {
            [OpType.REG]: "reg",
            [OpType.REG_STACK]: "reg",
            [OpType.REG_GPR]: "gpr",
            [OpType.IMM]: "imm",
            [OpType.MEM]: "[addr]",
            [OpType.REGADDR]: "[reg±off]",
            [OpType.FP_REG]: "fp",
            [OpType.FP_IMM8]: "imm8",
            [OpType.FP_IMM16]: "imm16",
        };

        function buildMnemonicVariants() {
            const variants = {};
            for (const def of [...ISA, ...ISA_FP]) {
                const sig = def.sig.map((s) => SIG_LABELS[s] || "?").join(", ");
                const form = sig ? `${def.mnemonic} ${sig}` : def.mnemonic;
                if (!variants[def.mnemonic]) variants[def.mnemonic] = new Set();
                variants[def.mnemonic].add(form);
            }
            return variants;
        }
        const MNEMONIC_VARIANTS = buildMnemonicVariants();

        function mnemonicInfoDom(mnemonic) {
            const el = document.createElement("div");
            el.className = "cm-instr-info";
            const desc = document.createElement("div");
            desc.className = "cm-instr-desc";
            desc.textContent = MNEMONIC_INFO[mnemonic] || mnemonic;
            el.appendChild(desc);
            const forms = MNEMONIC_VARIANTS[mnemonic];
            if (forms) {
                for (const f of forms) {
                    const line = document.createElement("div");
                    line.className = "cm-instr-form";
                    line.textContent = f;
                    el.appendChild(line);
                }
            }
            return el;
        }

        const MNEMONIC_COMPLETIONS = [...MNEMONICS, ...MNEMONICS_FP].map((m) => ({
            label: m,
            info: () => mnemonicInfoDom(m),
            type: "keyword",
        }));

        const GPR_INFO = {
            A: "General purpose A",
            B: "General purpose B",
            C: "General purpose C",
            D: "General purpose D",
            SP: "Stack pointer",
            DP: "Data page",
        };
        const FP_WIDTH_LABELS = { 32: "float32", 16: "float16", 8: "ofp8", 4: "nf4" };
        const REGISTER_COMPLETIONS = [
            ...Object.keys(REGISTERS).map((r) => ({
                label: r,
                info: GPR_INFO[r] || r,
                type: "variable",
            })),
            ...Object.keys(FP_REGISTERS).map((r) => {
                const bits = FP_REGISTERS[r].bits;
                const fmt = FP_WIDTH_LABELS[bits] || bits + "b";
                return { label: r, info: `FP ${fmt}`, type: "variable" };
            }),
        ];

        function sim8CompletionSource(context) {
            const word = context.matchBefore(/[\w.]+/);
            if (!word || (word.from === word.to && !context.explicit)) return null;

            const prefix = word.text.toUpperCase();
            const line = context.state.doc.lineAt(word.from);
            const beforeWord = line.text.slice(0, word.from - line.from);
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
