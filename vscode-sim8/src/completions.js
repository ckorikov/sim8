"use strict";

const vscode = require("vscode");
const path = require("path");
const { isUrl } = require("./include-re");

// ── @directive completions ────────────────────────────────────────────────────

const TRIGGER_SUGGEST = { command: "editor.action.triggerSuggest", title: "" };

function buildDirectiveItems() {
  const page = new vscode.CompletionItem(
    "@page",
    vscode.CompletionItemKind.Keyword,
  );
  page.detail = "Set memory page";
  page.documentation = new vscode.MarkdownString(
    "Switch the assembler to the given memory page (0–255).",
  );
  page.insertText = new vscode.SnippetString("@page ${1:0}");
  page.filterText = "@page";

  // @include opens the quote and immediately triggers file suggestions.
  const include = new vscode.CompletionItem(
    "@include",
    vscode.CompletionItemKind.Keyword,
  );
  include.detail = "Include another file";
  include.documentation = new vscode.MarkdownString(
    "Include another assembly source file at this point.",
  );
  include.insertText = '@include "';
  include.filterText = "@include";
  include.command = TRIGGER_SUGGEST;

  return [page, include];
}

const DIRECTIVE_ITEMS = buildDirectiveItems();

// ── @include path completions ─────────────────────────────────────────────────

// Matches the partial path inside @include "..." (no closing quote) up to cursor.
const INCLUDE_PREFIX_RE = /^[ \t]*@include\s+"([^"]*)$/;

/**
 * @param {vscode.TextDocument} document
 * @param {vscode.Position} position
 * @param {string} linePrefix
 */
async function fileCompletions(document, position, linePrefix) {
  const m = INCLUDE_PREFIX_RE.exec(linePrefix);
  if (!m) return null;

  const typed = m[1];
  if (isUrl(typed)) return null;

  const docDir = path.dirname(document.uri.fsPath);
  const searchDir = vscode.Uri.file(path.resolve(docDir, path.dirname(typed)));
  const prefix = path.basename(typed);

  let entries;
  try {
    entries = await vscode.workspace.fs.readDirectory(searchDir);
  } catch {
    return null;
  }

  // Replace everything typed after the opening quote.
  const typedStart = position.character - typed.length;
  const replaceRange = new vscode.Range(
    position.line,
    typedStart,
    position.line,
    position.character,
  );

  const dirPrefix = typed.slice(0, typed.length - prefix.length);

  return entries
    .filter(([name]) => name.startsWith(prefix))
    .map(([name, type]) => {
      const isDir = type === vscode.FileType.Directory;
      const item = new vscode.CompletionItem(
        name,
        isDir
          ? vscode.CompletionItemKind.Folder
          : vscode.CompletionItemKind.File,
      );
      // Directories re-trigger suggestions; files close the quote.
      item.insertText = dirPrefix + name + (isDir ? "/" : '"');
      item.range = replaceRange;
      item.detail = isDir ? "directory" : "file";
      if (isDir) item.command = TRIGGER_SUGGEST;
      return item;
    });
}

// ── Provider ──────────────────────────────────────────────────────────────────

/** @param {vscode.ExtensionContext} context */
function registerCompletionProvider(context) {
  const provider = vscode.languages.registerCompletionItemProvider(
    "sim8asm",
    {
      async provideCompletionItems(document, position) {
        const linePrefix = document
          .lineAt(position)
          .text.slice(0, position.character);

        if (INCLUDE_PREFIX_RE.test(linePrefix)) {
          return fileCompletions(document, position, linePrefix);
        }

        if (linePrefix.trimStart().startsWith("@")) {
          const atCol = linePrefix.indexOf("@");
          const replaceRange = new vscode.Range(
            position.line,
            atCol,
            position.line,
            position.character,
          );
          return DIRECTIVE_ITEMS.map((item) =>
            Object.assign(
              new vscode.CompletionItem(item.label, item.kind),
              item,
              {
                range: replaceRange,
              },
            ),
          );
        }

        return null;
      },
    },
    "@",
    '"',
    "/",
  );
  context.subscriptions.push(provider);
}

module.exports = { registerCompletionProvider };
