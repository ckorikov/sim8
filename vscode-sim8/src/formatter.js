"use strict";

const INDENT = "    "; // 4 spaces

/**
 * Format a single line of sim8 assembly.
 *
 * Rules:
 * - Blank lines and comment-only lines pass through (trimmed).
 * - @directives: no indent, lowercase directive, preserve args.
 * - Labels: column 0, lowercase name, colon.
 * - Instructions: 8-space indent, UPPERCASE mnemonic (with suffixes), preserve operands.
 * - Inline comments: aligned to a consistent column.
 */
function formatLine(raw) {
  const trimmed = raw.trim();
  if (trimmed === "") return "";
  if (trimmed.startsWith(";")) return trimmed;

  // Split off inline comment
  let code = trimmed;
  let comment = "";
  const semi = _findCommentStart(trimmed);
  if (semi !== -1) {
    code = trimmed.slice(0, semi).trimEnd();
    comment = trimmed.slice(semi);
  }

  // @directive
  if (code.startsWith("@")) {
    const result = code.replace(/^@\w+/, (m) => m.toLowerCase());
    return _appendComment(result, comment);
  }

  // Label definition: "name:" possibly followed by instruction or data
  const labelMatch = code.match(/^(\.?[A-Za-z_]\w*)\s*:(.*)/);
  if (labelMatch) {
    const label = labelMatch[1].toLowerCase() + ":";
    const rest = labelMatch[2].trim();
    if (rest === "") {
      return _appendComment(label, comment);
    }
    // Label with instruction on same line (e.g., "data: DB 1, 2")
    const formatted = _formatInstruction(rest);
    return _appendComment(`${label} ${formatted}`, comment);
  }

  // Instruction
  return _appendComment(INDENT + _formatInstruction(code), comment);
}

/**
 * Format an instruction: UPPERCASE mnemonic, clean operand spacing.
 */
function _formatInstruction(code) {
  const parts = code.match(/^(\S+)(.*)/);
  if (!parts) return code;

  const mnemonic = parts[1].toUpperCase();
  const operandStr = parts[2].trim();

  if (operandStr === "") return mnemonic;

  // Normalize operand spacing: collapse whitespace around commas
  const operands = operandStr
    .split(",")
    .map((s) => s.trim())
    .join(", ");

  return `${mnemonic} ${operands}`;
}

/**
 * Find the start of an inline comment, ignoring semicolons inside strings.
 */
function _findCommentStart(line) {
  let inDouble = false;
  let inSingle = false;
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === '"' && !inSingle) inDouble = !inDouble;
    else if (ch === "'" && !inDouble) inSingle = !inSingle;
    else if (ch === ";" && !inDouble && !inSingle) return i;
  }
  return -1;
}

const COMMENT_COL = 30;

/**
 * Append inline comment, padded to COMMENT_COL if it fits.
 */
function _appendComment(code, comment) {
  if (!comment) return code;
  if (code.length >= COMMENT_COL) {
    return `${code} ${comment}`;
  }
  return code.padEnd(COMMENT_COL) + comment;
}

/**
 * Format entire document.
 */
function formatDocument(text) {
  return text.split("\n").map(formatLine).join("\n");
}

/** @param {import("vscode").ExtensionContext} context */
function registerFormattingProvider(context) {
  const vscode = require("vscode");
  const provider = vscode.languages.registerDocumentFormattingEditProvider(
    "sim8asm",
    {
      provideDocumentFormattingEdits(document) {
        const text = document.getText();
        const formatted = formatDocument(text);
        if (formatted === text) return [];
        const fullRange = new vscode.Range(
          document.positionAt(0),
          document.positionAt(text.length),
        );
        return [vscode.TextEdit.replace(fullRange, formatted)];
      },
    },
  );
  context.subscriptions.push(provider);
}

module.exports = { registerFormattingProvider, formatDocument };
