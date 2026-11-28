// Writes the messages of the calculator's bare-metal and Image tests and the output that each must
// give, from Node's BigInt alone.
//
//   node messages.mjs DIR [COUNT]
//
// For each message NAME, DIR/NAME.in holds the input of the bare-metal program, the length in
// eight bytes, the lowest first, followed by the message, and DIR/NAME.want the bytes that the
// program must write: the number of words of the line in eight bytes, the line, and zeros to the
// end of its last word.  DIR/NAME.line holds the line alone, which the Image writes before its
// status byte.  The messages cover every operation on random operands from one digit to about
// 600, the values 0, ±1, ±(2^32 - 1), ±2^32, and ±(2^64 - 1), zero divisors, operands outside the
// grammar, names of no operation, wrong numbers of spaces, empty parts, a message of 65,536 bytes, and one of
// 65,537 bytes.  A message with an empty part, from a leading, a trailing, or a doubled space, gives
// the line 4.  COUNT, when given, keeps the first COUNT messages.
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const [dir, countArg] = process.argv.slice(2);
mkdirSync(dir, { recursive: true });

const grammar = /^(0|-?[1-9][0-9]*)$/;
const ops = ['cmp', 'add', 'sub', 'mul', 'tdiv', 'tmod', 'ediv', 'emod'];
const divides = new Set(['tdiv', 'tmod', 'ediv', 'emod']);

function ediv(a, b) {
  let r = a % b;
  if (r < 0n) r += b < 0n ? -b : b;
  return [(a - r) / b, r];
}

function apply(op, a, b) {
  switch (op) {
    case 'cmp': return a < b ? -1n : a === b ? 0n : 1n;
    case 'add': return a + b;
    case 'sub': return a - b;
    case 'mul': return a * b;
    case 'tdiv': return a / b;
    case 'tmod': return a % b;
    case 'ediv': return ediv(a, b)[0];
    case 'emod': return ediv(a, b)[1];
  }
  throw new Error(op);
}

// The line of a message given as bytes, as the specification's calcSpec defines it.
function line(bytes) {
  if (bytes.length > 65536) return '4';
  const parts = [];
  let cur = [];
  for (const c of bytes) {
    if (c === 32) { parts.push(cur); cur = []; } else cur.push(c);
  }
  parts.push(cur);
  if (parts.some((p) => p.length === 0)) return '4';
  const text = (p) => Buffer.from(p).toString('latin1');
  const read = (p) => {
    const s = text(p);
    return p.every((c) => c < 128) && grammar.test(s) ? BigInt(s) : null;
  };
  if (parts.length === 2) {
    if (text(parts[0]) !== 'neg') return '4';
    const a = read(parts[1]);
    return a === null ? '1' : `0 ${-a}`;
  }
  if (parts.length === 3) {
    const op = text(parts[0]);
    if (!ops.includes(op)) return '4';
    const a = read(parts[1]);
    if (a === null) return '1';
    const b = read(parts[2]);
    if (b === null) return '2';
    if (divides.has(op) && b === 0n) return '3';
    return `0 ${apply(op, a, b)}`;
  }
  return '4';
}

let seed = 0x2545f4914f6cdd1dn;
function next() {
  seed ^= seed << 13n; seed &= (1n << 64n) - 1n;
  seed ^= seed >> 7n;
  seed ^= seed << 17n; seed &= (1n << 64n) - 1n;
  return seed;
}
function digits(n) {
  let s = String(1n + (next() % 9n));
  while (s.length < n) s += String(next() % 10n);
  return s;
}
function randomInt(maxDigits) {
  const n = 1 + Number(next() % BigInt(maxDigits));
  const s = digits(n);
  return next() % 2n === 0n ? s : `-${s}`;
}

const cases = [];
const add = (name, msg) => cases.push([name, Buffer.isBuffer(msg) ? msg : Buffer.from(msg, 'latin1')]);

const edges = ['0', '1', '-1', '4294967295', '-4294967295', '4294967296', '-4294967296',
  '18446744073709551615', '-18446744073709551615', '7', '-7'];
for (const op of ops) {
  for (const a of edges) for (const b of edges) add(`${op}-e-${cases.length}`, `${op} ${a} ${b}`);
  for (let i = 0; i < 12; i++) add(`${op}-r-${cases.length}`, `${op} ${randomInt(600)} ${randomInt(600)}`);
}
for (const a of edges) add(`neg-e-${cases.length}`, `neg ${a}`);
for (let i = 0; i < 8; i++) add(`neg-r-${cases.length}`, `neg ${randomInt(600)}`);
const malformed = ['', 'add', 'add 1', 'add 1 2 3', 'neg 1 2', 'neg', 'foo 1 2', 'add  1 2',
  'add 1 2 ', ' add 1 2', 'ADD 1 2', 'add -0 1', 'add 01 1', 'add 1 +2', 'add 1 x', 'add - 1',
  'add 1 -', 'tdiv 5 0', 'emod -5 0', 'neg -0', 'neg 00', 'cmp 1 1', 'cmp -2 3', 'cmp 3 -2',
  'tdi 1 2', 'tdivv 1 2', 'neg x', 'add  1', 'add  ', 'add 1 ', 'neg ', 'cmp  0', 'tdiv 1 '];
for (const m of malformed) add(`m-${cases.length}`, m);
add(`m-${cases.length}`, Buffer.from([0x61, 0x64, 0x64, 0x20, 0xb1, 0x20, 0x32]));
add(`m-${cases.length}`, Buffer.from([0x61, 0x64, 0x64, 0x20, 0x31, 0x20, 0x00]));
// A product of two operands that fills 65,536 bytes, and the same message with one more byte.
const longMsg = `mul ${digits(32765)} -${digits(32765)}`;
add('long-65536', longMsg);
add('long-65537', `${longMsg}1`);

const keep = countArg ? cases.slice(0, Number(countArg)) : cases;
for (const [name, msg] of keep) {
  const len = Buffer.alloc(8);
  len.writeBigUInt64LE(BigInt(msg.length));
  writeFileSync(join(dir, `${name}.in`), Buffer.concat([len, msg]));
  const l = Buffer.from(line([...msg]), 'latin1');
  const words = Math.ceil(l.length / 8);
  const head = Buffer.alloc(8);
  head.writeBigUInt64LE(BigInt(words));
  writeFileSync(join(dir, `${name}.want`), Buffer.concat([head, l, Buffer.alloc(words * 8 - l.length)]));
  writeFileSync(join(dir, `${name}.line`), l);
}
console.log(`messages: ${keep.length} of ${cases.length}`);
