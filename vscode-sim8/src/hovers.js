"use strict";

const vscode = require("vscode");

// Resolved by esbuild at bundle time from web/lib/
const {
  ISA,
  ISA_FP,
  MNEMONIC_ALIASES,
  MNEMONICS_FP,
  FP_CONTROL_MNEMONICS,
} = require("../../web/lib/isa.js");

const {
  MNEMONIC_INFO,
  MNEMONIC_FLAGS,
  MNEMONIC_FP_EXCEPTIONS,
  MNEMONIC_NOTES,
  SIG_LABELS,
  FP_FORMAT_DOCS,
  REGISTER_DOCS,
  DIRECTIVE_DOCS,
} = require("../../web/lib/isa-docs.js");

// ── Build syntax forms from ISA tables ───────────────────────────────────────

function buildSyntaxForms() {
  const forms = {};
  for (const def of [...ISA, ...ISA_FP]) {
    const sig = def.sig.map((s) => SIG_LABELS[s] ?? "?").join(", ");
    const form = sig ? `${def.mnemonic} ${sig}` : def.mnemonic;
    if (!forms[def.mnemonic]) forms[def.mnemonic] = new Set();
    forms[def.mnemonic].add(form);
  }
  // DB is a pseudo-instruction not in ISA tables
  forms.DB = new Set(["DB imm8 [, ...]", 'DB "string"', "DB float_f [, ...]"]);
  return forms;
}

const SYNTAX_FORMS = buildSyntaxForms();

// FP mnemonics that take format suffixes (all FP except control)
const FP_WITH_SUFFIX = [...MNEMONICS_FP].filter(
  (m) => !FP_CONTROL_MNEMONICS.has(m),
);
const FP_INSTR_RE = new RegExp(
  `^(${FP_WITH_SUFFIX.join("|")})((?:\\.(?:E\\d+M\\d+|BF|O[23]|N[12]|[FH]))+)$`,
  "i",
);

// ── Main lookup ───────────────────────────────────────────────────────────────

function buildHoverContent(word) {
  const upper = word.toUpperCase();
  const canonical = MNEMONIC_ALIASES[upper];
  const resolved = canonical ?? upper;

  if (REGISTER_DOCS[resolved]) return registerHover(resolved);
  if (DIRECTIVE_DOCS[resolved]) return directiveHover(resolved);

  const fpMatch = resolved.match(FP_INSTR_RE);
  if (fpMatch)
    return mnemonicHover(fpMatch[1], fpMatch[2], canonical ? upper : null);

  if (MNEMONIC_INFO[resolved])
    return mnemonicHover(resolved, null, canonical ? upper : null);

  return null;
}

// ── Hover builders ────────────────────────────────────────────────────────────

function mnemonicHover(mnemonic, suffix, aliasOf) {
  const md = new vscode.MarkdownString("", true);

  const title = suffix
    ? `**${mnemonic}${suffix}**`
    : aliasOf
      ? `**${aliasOf}** *(alias for ${mnemonic})*`
      : `**${mnemonic}**`;
  md.appendMarkdown(`${title}\n\n`);
  const info = MNEMONIC_INFO[mnemonic];
  if (info) md.appendMarkdown(info + "\n\n");

  const forms = SYNTAX_FORMS[mnemonic];
  if (forms?.size) {
    md.appendMarkdown("**Syntax:**  \n");
    for (const f of forms) md.appendMarkdown(`\`${f}\`  \n`);
  }

  if (suffix) {
    md.appendMarkdown("\n**Format:**\n");
    for (const p of suffix.split(".").filter(Boolean)) {
      const fmt = FP_FORMAT_DOCS[p.toUpperCase()];
      if (!fmt) continue;
      let line = `- **.${p}** → ${fmt.name} (${fmt.exmy}, ${fmt.bits}-bit, ${fmt.registers})`;
      if (fmt.note) line += ` — *${fmt.note}*`;
      md.appendMarkdown(line + "\n");
    }
  }

  const flags = MNEMONIC_FLAGS[mnemonic];
  if (flags) md.appendMarkdown(`\n**Flags:** ${flags}\n`);

  const fpex = MNEMONIC_FP_EXCEPTIONS[mnemonic];
  if (fpex) md.appendMarkdown(`\n**FP exceptions:** ${fpex}\n`);

  const note = MNEMONIC_NOTES[mnemonic];
  if (note) md.appendMarkdown(`\n> ${note}\n`);

  return md;
}

function registerHover(name) {
  const md = new vscode.MarkdownString("", true);
  const { type, description } = REGISTER_DOCS[name];
  md.appendMarkdown(`**${name}** *(${type})*\n\n${description}\n`);
  return md;
}

function directiveHover(name) {
  const md = new vscode.MarkdownString("", true);
  const { description, syntax, note } = DIRECTIVE_DOCS[name];
  md.appendMarkdown(`**${name}**\n\n${description}\n\n`);
  if (syntax?.length) {
    md.appendMarkdown("**Syntax:**  \n");
    for (const s of syntax) md.appendMarkdown(`\`${s}\`  \n`);
  }
  if (note) md.appendMarkdown(`\n${note}\n`);
  return md;
}

module.exports = { buildHoverContent };
