#!/usr/bin/env node
"use strict";

const fs = require("fs");
const { formatDocument } = require("../src/formatter");

const args = process.argv.slice(2);

if (args.includes("--help") || args.includes("-h")) {
  process.stderr.write("Usage: sim8-fmt [file.asm ...]\n");
  process.stderr.write("  No args: read stdin, write stdout\n");
  process.stderr.write("  With files: format in place\n");
  process.exit(0);
}

if (args.length === 0) {
  const input = fs.readFileSync("/dev/stdin", "utf8");
  process.stdout.write(formatDocument(input));
} else {
  for (const file of args) {
    const input = fs.readFileSync(file, "utf8");
    const output = formatDocument(input);
    if (input !== output) {
      fs.writeFileSync(file, output, "utf8");
      process.stderr.write(`formatted: ${file}\n`);
    }
  }
}
