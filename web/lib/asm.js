/**
 * Two-pass assembler for sim8 ISA v2.
 * Port of pysim8/src/pysim8/asm/parser.py + codegen.py
 * Single ES module, zero DOM dependency.
 */

import {
  Op, OpType, BY_MNEMONIC, BY_MNEMONIC_FP,
  REGISTERS, MNEMONICS, MNEMONICS_FP, FP_CONTROL_MNEMONICS, MNEMONIC_ALIASES,
  GPR_CODES, STACK_CODES, FP_REGISTERS, FP_SUFFIX_TO_FMT,
  FP_FMT_WIDTH, FP_WIDTH_REGS, FP_FMT_F, FP_FMT_N1, FP_FMT_N2,
  FP_DB_SUFFIX_TO_FMT,
  encodeRegaddr, encodeFpm,
} from './isa.js';

import { floatToBytes } from './fp.js';

// ── Error ────────────────────────────────────────────────────────

export class AsmError extends Error {
  constructor(message, line) {
    super(`Line ${line}: ${message}`);
    this.message = message;
    this.line = line;
  }
}

// ── Cached combined mnemonic set (v2) ────────────────────────────

const ALL_MNEMONICS_V2 = new Set([...MNEMONICS, ...MNEMONICS_FP]);

// ── Operand tags ─────────────────────────────────────────────────

const TAG_REG = 'reg';
const TAG_CONST = 'const';
const TAG_ADDR = 'addr';
const TAG_REGADDR = 'regaddr';
const TAG_STRING = 'string';
const TAG_LABEL = 'label';
const TAG_ADDR_LABEL = 'addr_label';
const TAG_FP_REG = 'fp_reg';
const TAG_FLOAT = 'float';
const TAG_FP_IMM = 'fp_imm';

// ── Number parsing ───────────────────────────────────────────────

const _RE_HEX = /^0x([0-9A-Fa-f]+)$/;
const _RE_OCT = /^0o([0-7]+)$/;
const _RE_BIN = /^([01]+)b$/;
const _RE_DEC_EXPLICIT = /^(\d+)d$/;
const _RE_DEC = /^(\d+)$/;
const _RE_CHAR = /^'(.)'$/;
const _RE_CHAR_MULTI = /^'(.{2,})'$/;

const _NUM_FORMATS = [
  [_RE_HEX, 16],
  [_RE_OCT, 8],
  [_RE_BIN, 2],
  [_RE_DEC_EXPLICIT, 10],
  [_RE_DEC, 10],
];

function _tryParseNumber(token) {
  let m = _RE_CHAR_MULTI.exec(token);
  if (m) return null;
  m = _RE_CHAR.exec(token);
  if (m) return m[1].charCodeAt(0);
  for (const [pattern, base] of _NUM_FORMATS) {
    m = pattern.exec(token);
    if (m) return parseInt(m[1], base);
  }
  return null;
}

function _parseNumber(token, line) {
  if (_RE_CHAR_MULTI.test(token)) {
    throw new AsmError('Only one character is allowed', line);
  }
  const val = _tryParseNumber(token);
  if (val === null) {
    throw new AsmError('Invalid number format', line);
  }
  return val;
}

function _checkByteRange(value, line) {
  if (value < 0 || value > 255) {
    throw new AsmError(`${value} must have a value between 0-255`, line);
  }
  return value;
}

// ── Label regex ──────────────────────────────────────────────────

const _RE_LABEL = /^[.A-Za-z]\w*$/;

// ── Float literal parsing ────────────────────────────────────────

const _RE_FLOAT = /^([+-]?)(\d+\.\d*|\.\d+)([eE][+-]?\d+)?(_\w+)?$/;
const _RE_FLOAT_SPECIAL = /^([+-]?)(inf|nan)(_\w+)?$/i;

// ── Bracket operand parsing ──────────────────────────────────────

const _RE_BRACKET = /^\[(.+)\]$/;
const _RE_REG_OFFSET = /^([A-Za-z]+)\s*([+-])\s*(\d+)$/;
const _RE_REG_ONLY = /^([A-Za-z]+)$/;

function _parseBracketOperand(inner, line) {
  inner = inner.trim();

  // [reg+-offset]
  let m = _RE_REG_OFFSET.exec(inner);
  if (m) {
    const regName = m[1].toUpperCase();
    const sign = m[2];
    let offsetVal = parseInt(m[3], 10);
    if (sign === '-') offsetVal = -offsetVal;
    if (!(regName in REGISTERS)) {
      throw new AsmError(`Invalid register in address: ${m[1]}`, line);
    }
    if (offsetVal < -16 || offsetVal > 15) {
      throw new AsmError('offset must be a value between -16...+15', line);
    }
    return { tag: TAG_REGADDR, regCode: REGISTERS[regName], offset: offsetVal };
  }

  // [reg]
  m = _RE_REG_ONLY.exec(inner);
  if (m) {
    const regName = m[1].toUpperCase();
    if (regName in REGISTERS) {
      return { tag: TAG_REGADDR, regCode: REGISTERS[regName], offset: 0 };
    }
  }

  // [number]
  const val = _tryParseNumber(inner);
  if (val !== null) {
    _checkByteRange(val, line);
    return { tag: TAG_ADDR, value: val };
  }

  // [label]
  if (_RE_LABEL.test(inner)) {
    return { tag: TAG_ADDR_LABEL, name: inner.toLowerCase() };
  }

  throw new AsmError(`Invalid address: ${inner}`, line);
}

// ── Operand parsers ──────────────────────────────────────────────

function _tryBracket(token, line) {
  const m = _RE_BRACKET.exec(token);
  if (m) return _parseBracketOperand(m[1], line);
  return null;
}

function _tryRegister(token, _line) {
  const up = token.toUpperCase();
  if (up in REGISTERS) {
    return { tag: TAG_REG, code: REGISTERS[up] };
  }
  if (up in FP_REGISTERS) {
    const r = FP_REGISTERS[up];
    return { tag: TAG_FP_REG, name: up, pos: r.pos, fmt: r.fmt, phys: r.phys };
  }
  return null;
}

function _tryString(token, _line) {
  if (token.startsWith('"') && token.endsWith('"')) {
    return { tag: TAG_STRING, text: token.slice(1, -1) };
  }
  return null;
}

function _tryConst(token, line) {
  if (_RE_CHAR_MULTI.test(token)) {
    throw new AsmError('Only one character is allowed', line);
  }
  const val = _tryParseNumber(token);
  if (val !== null) {
    _checkByteRange(val, line);
    return { tag: TAG_CONST, value: val };
  }
  return null;
}

// ── Shared float parsing ─────────────────────────────────────────

function _resolveFloatSuffix(suffixStr, line, defaultFmt, rejectNarrow) {
  if (suffixStr == null) return defaultFmt;
  const suffix = suffixStr.slice(1).toUpperCase();
  if (!(suffix in FP_DB_SUFFIX_TO_FMT)) {
    throw new AsmError('Invalid float literal', line);
  }
  const fmt = FP_DB_SUFFIX_TO_FMT[suffix];
  if (rejectNarrow && (fmt === FP_FMT_N1 || fmt === FP_FMT_N2)) {
    throw new AsmError(
      `Unsupported float format for DB: ${suffixStr.slice(1)}`, line
    );
  }
  return fmt;
}

function _parseFloatValue(token, line, tag, defaultFmt, rejectNarrow) {
  let m = _RE_FLOAT_SPECIAL.exec(token);
  if (m) {
    const fmt = _resolveFloatSuffix(m[3] || null, line, defaultFmt, rejectNarrow);
    let val;
    if (m[2].toLowerCase() === 'inf') {
      val = m[1] === '-' ? -Infinity : Infinity;
    } else {
      val = NaN;
      if (m[1] === '-') val = -val;
    }
    return { tag, value: val, fmt };
  }

  m = _RE_FLOAT.exec(token);
  if (m) {
    const fmt = _resolveFloatSuffix(m[4] || null, line, defaultFmt, rejectNarrow);
    const text = (m[1] || '') + m[2] + (m[3] || '');
    const val = parseFloat(text);
    if (Number.isNaN(val) && text.toLowerCase() !== 'nan') {
      throw new AsmError('Invalid float literal', line);
    }
    return { tag, value: val, fmt };
  }

  return null;
}

function _tryFpImm(token, line) {
  return _parseFloatValue(token, line, TAG_FP_IMM, null, false);
}

function _tryLabel(token, _line) {
  if (_RE_LABEL.test(token)) {
    return { tag: TAG_LABEL, name: token.toLowerCase() };
  }
  return null;
}

const _OPERAND_PARSERS = [
  _tryBracket,
  _tryRegister,
  _tryString,
  _tryConst,
  _tryFpImm,
  _tryLabel,
];

function _parseOperand(token, line) {
  token = token.trim();
  for (const parser of _OPERAND_PARSERS) {
    const result = parser(token, line);
    if (result !== null) return result;
  }
  throw new AsmError(`Invalid operand: ${token}`, line);
}

// ── Float literal for DB ─────────────────────────────────────────

function _parseFloatLiteral(token, line) {
  return _parseFloatValue(token, line, TAG_FLOAT, FP_FMT_F, true);
}

// ── DB operand parsing ───────────────────────────────────────────

function _parseDbOperands(raw, line, arch) {
  raw = raw.trim();

  // String literal
  if (raw.startsWith('"') && raw.endsWith('"')) {
    return [{ tag: TAG_STRING, text: raw.slice(1, -1) }];
  }

  const parts = raw.split(',').map(p => p.trim());
  const operands = [];
  let hasFloat = false;
  let hasInt = false;

  for (const part of parts) {
    if (!part) continue;
    if (part.startsWith('[')) {
      throw new AsmError('DB does not support this operand', line);
    }
    const up = part.toUpperCase();
    if (up in REGISTERS) {
      throw new AsmError('DB does not support this operand', line);
    }

    // Try float literal first (if arch >= 2)
    if (arch >= 2) {
      const fp = _parseFloatLiteral(part, line);
      if (fp !== null) {
        if (hasInt) {
          throw new AsmError(
            'DB does not support mixing float and integer operands', line
          );
        }
        hasFloat = true;
        operands.push(fp);
        continue;
      }
    }

    // Integer value
    if (hasFloat) {
      throw new AsmError(
        'DB does not support mixing float and integer operands', line
      );
    }

    if (_RE_LABEL.test(part) && _tryParseNumber(part) === null) {
      throw new AsmError('DB does not support this operand', line);
    }

    hasInt = true;
    const val = _parseNumber(part, line);
    _checkByteRange(val, line);
    operands.push({ tag: TAG_CONST, value: val });
  }
  return operands;
}

// ── Line tokenization ────────────────────────────────────────────

function _tokenizeLine(line) {
  const result = [];
  let inString = false;
  let i = 0;
  while (i < line.length) {
    const ch = line[i];
    if (ch === '"') {
      inString = !inString;
    } else if (ch === "'" && !inString) {
      if (i + 2 < line.length && line[i + 2] === "'") {
        result.push(line[i], line[i + 1], line[i + 2]);
        i += 3;
        continue;
      }
    } else if (ch === ';' && !inString) {
      break;
    }
    result.push(ch);
    i += 1;
  }
  return result.join('').trim();
}

function _splitOperands(operandStr) {
  const parts = [];
  const current = [];
  let depth = 0;
  let inString = false;

  for (const ch of operandStr) {
    if (ch === '"') {
      inString = !inString;
    } else if (ch === '[' && !inString) {
      depth += 1;
    } else if (ch === ']' && !inString) {
      depth -= 1;
    } else if (ch === ',' && depth === 0 && !inString) {
      parts.push(current.join('').trim());
      current.length = 0;
      continue;
    }
    current.push(ch);
  }

  if (current.length > 0) {
    parts.push(current.join('').trim());
  }
  return parts.filter(p => p.length > 0);
}

// ── Line parsing ─────────────────────────────────────────────────

const _RE_LABEL_DEF = /^([.A-Za-z]\w*)\s*:/;

function _parseLine(raw, lineNo, arch) {
  const text = _tokenizeLine(raw);

  const result = {
    lineNo,
    label: null,
    mnemonic: null,
    operands: null,
    dstSuffix: null,
    srcSuffix: null,
  };

  if (!text) return result;

  let remaining = text;

  // Check for label
  const labelMatch = _RE_LABEL_DEF.exec(remaining);
  if (labelMatch) {
    const labelName = labelMatch[1];
    if (labelName.toUpperCase() in REGISTERS) {
      throw new AsmError(
        `Label contains keyword: ${labelName.toUpperCase()}`, lineNo
      );
    }
    if (arch >= 2 && labelName.toUpperCase() in FP_REGISTERS) {
      throw new AsmError(
        `Label contains keyword: ${labelName.toUpperCase()}`, lineNo
      );
    }
    result.label = labelName.toLowerCase();
    remaining = remaining.slice(labelMatch[0].length).trim();
  }

  if (!remaining) return result;

  // Split mnemonic from operands
  const spaceIdx = remaining.search(/\s/);
  let mnemonicRaw, operandStr;
  if (spaceIdx === -1) {
    mnemonicRaw = remaining.toUpperCase();
    operandStr = '';
  } else {
    mnemonicRaw = remaining.slice(0, spaceIdx).toUpperCase();
    operandStr = remaining.slice(spaceIdx + 1).trim();
  }

  // Resolve aliases
  let mnemonic = MNEMONIC_ALIASES[mnemonicRaw] || mnemonicRaw;

  // Check for FP mnemonic with dot-suffix
  let dstSuffix = null;
  let srcSuffix = null;
  if (mnemonic.includes('.') && arch >= 2) {
    const dotParts = mnemonic.split('.');
    const base = dotParts[0];
    if (MNEMONICS_FP.has(base)) {
      mnemonic = base;
      dstSuffix = dotParts.length > 1 ? dotParts[1] : null;
      srcSuffix = dotParts.length > 2 ? dotParts[2] : null;
      if (dotParts.length > 3) {
        throw new AsmError('Syntax error', lineNo);
      }
    }
  }

  const allMnemonics = arch < 2 ? MNEMONICS : ALL_MNEMONICS_V2;

  if (!allMnemonics.has(mnemonic)) {
    if (_RE_LABEL.test(mnemonicRaw)) {
      throw new AsmError(`Invalid instruction: ${mnemonicRaw}`, lineNo);
    }
    throw new AsmError('Syntax error', lineNo);
  }

  // Validate FP suffix requirements
  if (arch >= 2 && MNEMONICS_FP.has(mnemonic)) {
    if (FP_CONTROL_MNEMONICS.has(mnemonic)) {
      if (dstSuffix !== null) {
        throw new AsmError('Syntax error', lineNo);
      }
    } else if (mnemonic === 'FCVT') {
      if (dstSuffix === null || srcSuffix === null) {
        throw new AsmError('FP format suffix required', lineNo);
      }
    } else {
      if (dstSuffix === null) {
        throw new AsmError('FP format suffix required', lineNo);
      }
    }
  }

  result.mnemonic = mnemonic;
  result.dstSuffix = dstSuffix;
  result.srcSuffix = srcSuffix;

  // Parse operands based on mnemonic
  if (mnemonic === 'DB') {
    result.operands = _parseDbOperands(operandStr, lineNo, arch);
    return result;
  }

  if (mnemonic === 'HLT' || mnemonic === 'RET' || mnemonic === 'FCLR') {
    if (operandStr) {
      throw new AsmError(`${mnemonic}: too many arguments`, lineNo);
    }
    result.operands = [];
    return result;
  }

  // Split and parse operands
  if (operandStr) {
    const tokens = _splitOperands(operandStr);
    result.operands = tokens.map(t => _parseOperand(t, lineNo));
  } else {
    result.operands = [];
  }

  return result;
}

function _parseLines(source, arch) {
  const lines = source.split('\n');
  const parsed = [];
  const labelsSeen = {};

  for (let i = 0; i < lines.length; i++) {
    const lineNo = i + 1;
    const p = _parseLine(lines[i], lineNo, arch);

    if (p.label !== null) {
      if (p.label in labelsSeen) {
        throw new AsmError(`Duplicate label: ${p.label}`, lineNo);
      }
      labelsSeen[p.label] = lineNo;
    }

    parsed.push(p);
  }

  return parsed;
}

// ── Operand matching ─────────────────────────────────────────────

function _operandMatches(op, ot) {
  switch (ot) {
    case OpType.REG:
      return op.tag === TAG_REG;
    case OpType.REG_STACK:
      return op.tag === TAG_REG && STACK_CODES.has(op.code);
    case OpType.REG_GPR:
      return op.tag === TAG_REG && GPR_CODES.has(op.code);
    case OpType.IMM:
      return op.tag === TAG_CONST || op.tag === TAG_LABEL;
    case OpType.MEM:
      return op.tag === TAG_ADDR || op.tag === TAG_ADDR_LABEL;
    case OpType.REGADDR:
      return op.tag === TAG_REGADDR;
    case OpType.FP_REG:
      return op.tag === TAG_FP_REG;
    case OpType.FP_IMM8:
    case OpType.FP_IMM16:
      return op.tag === TAG_FP_IMM;
    default:
      return false;
  }
}

// ── Operand encoding ─────────────────────────────────────────────

function _encodeOperand(op) {
  switch (op.tag) {
    case TAG_REG:
      return op.code;
    case TAG_CONST:
      return op.value;
    case TAG_ADDR:
      return op.value;
    case TAG_REGADDR:
      return encodeRegaddr(op.regCode, op.offset);
    case TAG_LABEL:
      return 0; // placeholder for pass 2
    case TAG_ADDR_LABEL:
      return 0; // placeholder for pass 2
    default:
      throw new Error(`unexpected operand: ${op.tag}`);
  }
}

// ── Instruction matching ─────────────────────────────────────────

function _findInsn(mnemonic, operands, line, table) {
  if (table == null) table = BY_MNEMONIC;
  const candidates = table[mnemonic];
  if (!candidates) {
    throw new AsmError(`Invalid instruction: ${mnemonic}`, line);
  }

  for (const insn of candidates) {
    if (insn.sig.length !== operands.length) continue;
    let allMatch = true;
    for (let i = 0; i < insn.sig.length; i++) {
      if (!_operandMatches(operands[i], insn.sig[i])) {
        allMatch = false;
        break;
      }
    }
    if (allMatch) return insn;
  }

  let maxArity = 0;
  for (const insn of candidates) {
    if (insn.sig.length > maxArity) maxArity = insn.sig.length;
  }
  if (operands.length > maxArity) {
    throw new AsmError(`${mnemonic}: too many arguments`, line);
  }
  throw new AsmError(`${mnemonic} does not support this operand(s)`, line);
}

// ── DB encoding ──────────────────────────────────────────────────

function _encodeDbOperand(op, line, result) {
  if (op.tag === TAG_CONST) {
    result.push(op.value);
    return;
  }
  if (op.tag === TAG_STRING) {
    if (!op.text) {
      throw new AsmError('DB string must not be empty', line);
    }
    for (let i = 0; i < op.text.length; i++) {
      result.push(op.text.charCodeAt(i));
    }
    return;
  }
  if (op.tag === TAG_FLOAT) {
    const { data } = floatToBytes(op.value, op.fmt);
    for (let i = 0; i < data.length; i++) {
      result.push(data[i]);
    }
    return;
  }
  throw new AsmError(`DB does not support this operand`, line);
}

function _encodeDb(operands, line) {
  const result = [];
  for (const op of operands) {
    _encodeDbOperand(op, line, result);
  }
  return result;
}

// ── FP suffix validation ─────────────────────────────────────────

function _validateFpSuffix(suffix, line) {
  const upper = suffix.toUpperCase();
  if (!(upper in FP_SUFFIX_TO_FMT)) {
    throw new AsmError(`Invalid FP format suffix: .${suffix}`, line);
  }
  return FP_SUFFIX_TO_FMT[upper];
}

function _validateFpRegWidth(reg, fmt, line) {
  const fmtWidth = FP_FMT_WIDTH[fmt];
  const allowed = FP_WIDTH_REGS[fmtWidth];
  if (!allowed || !allowed.has(reg.name)) {
    throw new AsmError(
      'FP format suffix does not match register width', line
    );
  }
}

// ── FP instruction encoding ──────────────────────────────────────

function _encodeFpInstruction(insn, operands, dstSuffix, srcSuffix, line) {
  const dstFmt = dstSuffix ? _validateFpSuffix(dstSuffix, line) : null;
  const srcFmt = srcSuffix ? _validateFpSuffix(srcSuffix, line) : null;

  // FCVT special case: dual suffix
  if (insn.op === Op.FCVT_FP_FP) {
    if (dstFmt === srcFmt) {
      throw new AsmError('FCVT with identical formats (use FMOV)', line);
    }
    const dstReg = operands[0];
    const srcReg = operands[1];
    _validateFpRegWidth(dstReg, dstFmt, line);
    _validateFpRegWidth(srcReg, srcFmt, line);
    const dstFpm = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);
    const srcFpm = encodeFpm(srcReg.phys, srcReg.pos, srcFmt);
    return [insn.op, dstFpm, srcFpm];
  }

  // Separate FP reg operands from non-FP operands
  const fpOps = [];
  const nonFpOps = [];
  for (const op of operands) {
    if (op.tag === TAG_FP_REG) {
      _validateFpRegWidth(op, dstFmt, line);
      fpOps.push(op);
    } else {
      nonFpOps.push(op);
    }
  }

  // Encode FPM bytes
  const fpmBytes = fpOps.map(fp => encodeFpm(fp.phys, fp.pos, dstFmt));

  // Encode non-FP bytes
  const nonFpBytes = nonFpOps.map(op => _encodeOperand(op));

  return [insn.op, ...fpmBytes, ...nonFpBytes];
}

// ── FMOV immediate encoding ─────────────────────────────────────

function _encodeFmovImm(operands, dstSuffix, line) {
  if (operands[0].tag !== TAG_FP_REG) {
    throw new AsmError('FMOV does not support this operand(s)', line);
  }

  const dstReg = operands[0];
  const fpImm = operands[1];
  const dstFmt = _validateFpSuffix(dstSuffix, line);
  const fmtWidth = FP_FMT_WIDTH[dstFmt];

  if (fmtWidth === 32) {
    throw new AsmError('FP immediate not supported for float32', line);
  }
  if (fmtWidth === 4) {
    throw new AsmError('FP immediate not supported for 4-bit formats', line);
  }

  // Check literal suffix matches instruction suffix
  if (fpImm.fmt !== null && fpImm.fmt !== dstFmt) {
    throw new AsmError('FP immediate suffix mismatch', line);
  }

  _validateFpRegWidth(dstReg, dstFmt, line);

  const { data } = floatToBytes(fpImm.value, dstFmt);
  const fpmByte = encodeFpm(dstReg.phys, dstReg.pos, dstFmt);

  if (fmtWidth === 8) {
    return [Op.FMOV_FP_IMM8, fpmByte, data[0]];
  }
  // 16-bit
  return [Op.FMOV_FP_IMM16, fpmByte, data[0], data[1]];
}

// ── Instruction encoding ─────────────────────────────────────────

function _encodeInstruction(mnemonic, operands, line, dstSuffix, srcSuffix, arch) {
  if (mnemonic === 'DB') {
    return _encodeDb(operands, line);
  }

  if (arch >= 2 && MNEMONICS_FP.has(mnemonic)) {
    // FMOV immediate special case
    if (
      mnemonic === 'FMOV'
      && operands.length === 2
      && operands[1].tag === TAG_FP_IMM
    ) {
      return _encodeFmovImm(operands, dstSuffix, line);
    }

    const insn = _findInsn(mnemonic, operands, line, BY_MNEMONIC_FP);
    if (FP_CONTROL_MNEMONICS.has(mnemonic)) {
      // Control: no FPM, just opcode + operand bytes
      return [insn.op, ...operands.map(op => _encodeOperand(op))];
    }
    return _encodeFpInstruction(insn, operands, dstSuffix, srcSuffix, line);
  }

  const insn = _findInsn(mnemonic, operands, line, BY_MNEMONIC);
  return [insn.op, ...operands.map(op => _encodeOperand(op))];
}

// ── Two-pass assembly ────────────────────────────────────────────

export function assemble(source, arch = 2) {
  const parsed = _parseLines(source, arch);

  // Pass 1: generate code, collect labels
  const code = [];
  const labels = {};
  const mapping = {};
  const labelPatches = []; // [patchPos, labelName, lineNo]

  for (const pline of parsed) {
    const pos = code.length;

    if (pline.label !== null) {
      labels[pline.label] = pos;
    }

    if (pline.mnemonic === null) continue;

    const operands = pline.operands || [];

    const encoded = _encodeInstruction(
      pline.mnemonic, operands, pline.lineNo,
      pline.dstSuffix, pline.srcSuffix, arch,
    );

    if (pline.mnemonic !== 'DB') {
      mapping[pos] = pline.lineNo;
    }

    if (operands.length > 0) {
      for (let i = 0; i < operands.length; i++) {
        const op = operands[i];
        if (op.tag === TAG_LABEL || op.tag === TAG_ADDR_LABEL) {
          const isFpData = (
            arch >= 2
            && MNEMONICS_FP.has(pline.mnemonic)
            && !FP_CONTROL_MNEMONICS.has(pline.mnemonic)
          );
          if (isFpData) {
            let fpCount = 0;
            for (const o of operands) {
              if (o.tag === TAG_FP_REG) fpCount++;
            }
            let nonFpIdx = 0;
            for (let j = 0; j < i; j++) {
              if (operands[j].tag !== TAG_FP_REG) nonFpIdx++;
            }
            labelPatches.push([pos + 1 + fpCount + nonFpIdx, op.name, pline.lineNo]);
          } else {
            labelPatches.push([pos + 1 + i, op.name, pline.lineNo]);
          }
        }
      }
    }

    for (const byte of encoded) {
      code.push(byte);
    }
  }

  // Pass 2: resolve labels
  for (const [patchPos, labelName, lineNo] of labelPatches) {
    if (!(labelName in labels)) {
      throw new AsmError(`Undefined label: ${labelName}`, lineNo);
    }
    const addr = labels[labelName];
    if (addr < 0 || addr > 255) {
      throw new AsmError(`${addr} must have a value between 0-255`, lineNo);
    }
    code[patchPos] = addr;
  }

  return { code, labels, mapping };
}
