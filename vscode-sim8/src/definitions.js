"use strict";

const vscode = require("vscode");
const path = require("path");
const { INCLUDE_RE, isUrl } = require("./include-re");

// Matches a full @include "path" line; used to detect cursor-inside-path.
const INCLUDE_LINE_RE = /^[ \t]*@include\s+"([^"]*)"/;

function escapeRegex(s) {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function findInText(text, label) {
  const re = new RegExp(`^[ \\t]*(${escapeRegex(label)})\\s*:`, "im");
  const match = re.exec(text);
  if (!match) return -1;
  return match.index + match[0].indexOf(match[1]);
}

function collectIncludes(text, docUri) {
  const dir = path.dirname(docUri.fsPath);
  const uris = [];
  let m;
  INCLUDE_RE.lastIndex = 0;
  while ((m = INCLUDE_RE.exec(text)) !== null) {
    const p = m[1];
    if (isUrl(p)) continue;
    uris.push(vscode.Uri.file(path.resolve(dir, p)));
  }
  return uris;
}

function offsetToPosition(text, offset) {
  const before = text.slice(0, offset).replace(/\r\n/g, "\n");
  const lines = before.split("\n");
  return new vscode.Position(lines.length - 1, lines[lines.length - 1].length);
}

/**
 * If the cursor is inside the path of an @include "..." line, return a
 * Location pointing to that file (line 0). This makes Cmd+Click open the file.
 *
 * @param {vscode.TextDocument} document
 * @param {vscode.Position} position
 */
function includePathDefinition(document, position) {
  const line = document.lineAt(position).text;
  const m = INCLUDE_LINE_RE.exec(line);
  if (!m) return null;

  const p = m[1];
  const openQuoteIdx = m[0].indexOf('"');
  const pathStart = openQuoteIdx + 1;
  const pathEnd = pathStart + p.length;

  if (position.character < pathStart || position.character > pathEnd)
    return null;
  if (isUrl(p)) return null;

  const dir = path.dirname(document.uri.fsPath);
  const target = vscode.Uri.file(path.resolve(dir, p));
  return new vscode.Location(target, new vscode.Position(0, 0));
}

/**
 * @param {vscode.TextDocument} document
 * @param {string} label
 */
async function findLabelDefinition(document, label) {
  const text = document.getText();

  const localOffset = findInText(text, label);
  if (localOffset !== -1) {
    return new vscode.Location(document.uri, document.positionAt(localOffset));
  }

  for (const includeUri of collectIncludes(text, document.uri)) {
    try {
      const bytes = await vscode.workspace.fs.readFile(includeUri);
      const included = new TextDecoder().decode(bytes);
      const offset = findInText(included, label);
      if (offset === -1) continue;
      return new vscode.Location(
        includeUri,
        offsetToPosition(included, offset),
      );
    } catch {
      // File not found or unreadable — skip
    }
  }

  return null;
}

/** @param {vscode.ExtensionContext} context */
function registerDefinitionProvider(context) {
  const LABEL_RE = /\.?[A-Za-z_]\w*/;
  const provider = vscode.languages.registerDefinitionProvider("sim8asm", {
    provideDefinition(document, position) {
      const includeLink = includePathDefinition(document, position);
      if (includeLink) return includeLink;

      const range = document.getWordRangeAtPosition(position, LABEL_RE);
      if (!range) return null;
      return findLabelDefinition(document, document.getText(range));
    },
  });
  context.subscriptions.push(provider);
}

module.exports = { registerDefinitionProvider };
