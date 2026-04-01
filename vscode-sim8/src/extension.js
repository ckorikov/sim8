"use strict";

const vscode = require("vscode");
const { buildHoverContent } = require("./hovers");
const { registerCompletionProvider } = require("./completions");
const { registerDefinitionProvider } = require("./definitions");
const { registerFormattingProvider } = require("./formatter");

// Captures FP instructions with format suffixes (FADD.H, FCVT.F.H), @directives
const WORD_RE =
  /[@A-Za-z_]\w*(?:\.(?:E\d+M\d+|BF|O[23]|N[12]|[FHUI]|VV|VS|VI|R|EQ|NE|LT|LE|GT|GE))*/;

/** @param {vscode.ExtensionContext} context */
function activate(context) {
  const hoverProvider = vscode.languages.registerHoverProvider("sim8asm", {
    provideHover(document, position) {
      const range = document.getWordRangeAtPosition(position, WORD_RE);
      if (!range) return;
      const content = buildHoverContent(document.getText(range));
      if (!content) return;
      return new vscode.Hover(content, range);
    },
  });

  context.subscriptions.push(hoverProvider);
  registerCompletionProvider(context);
  registerDefinitionProvider(context);
  registerFormattingProvider(context);
}

// VS Code requires this export even when there's nothing to clean up.
function deactivate() {}

module.exports = { activate, deactivate };
