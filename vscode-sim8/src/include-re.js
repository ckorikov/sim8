"use strict";

// Shared regex — reset lastIndex before each use (stateful `g` flag).
const INCLUDE_RE = /^[ \t]*@include\s+"([^"]+)"/gim;

const isUrl = (s) => /^\w+:\/\//.test(s);

module.exports = { INCLUDE_RE, isUrl };
