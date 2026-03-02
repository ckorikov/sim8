/**
 * CodeMirror editor: initialization, syntax highlighting, execution line marking.
 */

import { MNEMONICS, MNEMONICS_FP, REGISTERS, FP_REGISTERS } from '../lib/isa.js';

const ALL_MNEMONICS_RE = new RegExp(
  '\\b(' + [...MNEMONICS, ...MNEMONICS_FP].join('|') + ')\\b', 'i'
);
const ALL_REGISTERS_RE = new RegExp(
  '\\b(' + [...Object.keys(REGISTERS), ...Object.keys(FP_REGISTERS)].join('|') + ')\\b'
);

let cmView = null;
let cmExecEffect = null;
let cmScrollIntoView = null;

export function highlightExecLine(line) {
  if (!cmView || !cmExecEffect) return;
  cmView.dispatch({ effects: cmExecEffect.of(line) });
  if (cmScrollIntoView && line >= 1 && line <= cmView.state.doc.lines) {
    const pos = cmView.state.doc.line(line).from;
    cmView.dispatch({ effects: cmScrollIntoView(pos, { y: 'center' }) });
  }
}

export function getEditorSource() {
  return cmView
    ? cmView.state.doc.toString()
    : document.querySelector('#editor-container textarea')?.value || '';
}

export async function initEditor(container, defaultCode) {
  try {
    const { EditorView, basicSetup } = await import('https://esm.sh/codemirror');
    const { EditorState, StateEffect, StateField } = await import('https://esm.sh/@codemirror/state');
    const { Decoration, GutterMarker, gutter } = await import('https://esm.sh/@codemirror/view');
    const { StreamLanguage, HighlightStyle, syntaxHighlighting } = await import('https://esm.sh/@codemirror/language');
    const { tags } = await import('https://esm.sh/@lezer/highlight');

    const setExecLine = StateEffect.define();
    cmExecEffect = setExecLine;
    const execLineDeco = Decoration.line({ class: 'cm-exec-line' });

    class ExecMarker extends GutterMarker {
      toDOM() {
        const el = document.createElement('span');
        el.textContent = '\u25B6';
        el.className = 'cm-exec-arrow';
        return el;
      }
    }
    const execMarker = new ExecMarker();

    const execLineField = StateField.define({
      create() { return { line: -1, decos: Decoration.none }; },
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
    const execDecoExt = EditorView.decorations.from(execLineField, s => s.decos);
    const execGutter = gutter({
      class: 'cm-exec-gutter',
      lineMarker(view, line) {
        const state = view.state.field(execLineField);
        if (state.line < 1) return null;
        const execLine = view.state.doc.line(state.line);
        return line.from === execLine.from ? execMarker : null;
      },
    });

    const asmLang = StreamLanguage.define({
      token(s) {
        if (s.match(/;.*/)) return 'comment';
        if (s.match(ALL_MNEMONICS_RE)) return 'keyword';
        if (s.match(ALL_REGISTERS_RE)) return 'variableName';
        if (s.match(/\b0x[0-9A-Fa-f]+\b/)) return 'number';
        if (s.match(/\b[0-9]+(\.[0-9]+)?\b/)) return 'number';
        if (s.match(/'[^']*'/) || s.match(/"[^"]*"/)) return 'string';
        if (s.match(/\[.*?\]/)) return 'bracket';
        if (s.match(/\.?\w+:/)) return 'labelName';
        s.next(); return null;
      },
    });

    const sim8Theme = EditorView.theme({
      '&': { height: '100%', background: 'var(--t-canvas)', color: 'var(--t-mid)' },
      '.cm-scroller': { fontFamily: "'JetBrains Mono', monospace", fontSize: '12px', lineHeight: '1.6' },
      '.cm-gutters': { background: 'var(--t-nav)', borderRight: '1px solid var(--t-border)', color: 'var(--t-dim)', minWidth: '36px' },
      '.cm-gutter': { fontSize: '11px' },
      '.cm-activeLine': { background: 'rgba(204,85,0,0.04)' },
      '.cm-activeLineGutter': { background: 'rgba(204,85,0,0.06)', color: 'var(--t-dim)' },
      '.cm-cursor': { borderLeftColor: 'var(--a-orange)', borderLeftWidth: '1.5px' },
      '.cm-selectionBackground': { background: 'var(--a-orange-a20) !important' },
      '.cm-matchingBracket': { background: 'var(--a-orange-a20)', color: 'var(--a-orange) !important' },
      '.cm-searchMatch': { background: 'var(--a-orange-a20)' },
      '.cm-foldPlaceholder': { background: 'var(--t-surface)', border: '1px solid var(--t-border)', color: 'var(--t-dim)' },
      '.cm-tooltip': { background: 'var(--t-surface)', border: '1px solid var(--t-border)', color: 'var(--t-text)' },
      '.cm-panels': { background: 'var(--t-nav)', borderTop: '1px solid var(--t-border)', color: 'var(--t-mid)' },
    }, { dark: true });

    const sim8Highlight = HighlightStyle.define([
      { tag: tags.keyword,      class: 'cm-hl-kw' },
      { tag: tags.variableName, class: 'cm-hl-var' },
      { tag: tags.number,       class: 'cm-hl-num' },
      { tag: tags.string,       class: 'cm-hl-str' },
      { tag: tags.comment,      class: 'cm-hl-cmt' },
      { tag: tags.bracket,      class: 'cm-hl-brk' },
      { tag: tags.labelName,    class: 'cm-hl-lbl' },
    ]);

    cmScrollIntoView = EditorView.scrollIntoView;
    cmView = new EditorView({
      state: EditorState.create({ doc: defaultCode, extensions: [
        basicSetup, asmLang,
        sim8Theme,
        syntaxHighlighting(sim8Highlight),
        execLineField, execDecoExt, execGutter,
      ] }),
      parent: container,
    });
  } catch (e) {
    console.warn('CodeMirror failed to load, using textarea fallback:', e);
    const ta = document.createElement('textarea');
    ta.style.cssText = "width:100%;height:100%;background:var(--t-canvas);color:var(--t-text);padding:16px;resize:none;outline:none;border:none;font-family:'JetBrains Mono',monospace;font-size:13px;tab-size:4;";
    ta.value = defaultCode;
    ta.spellcheck = false;
    container.appendChild(ta);
  }
}
