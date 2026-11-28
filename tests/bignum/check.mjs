// Tests the module of Library.Numerics.Bignum.Compiled against Node's BigInt, with no packages.  Every
// result must equal the canonical form of the exact result: the limbs of |z| with no zero limb at
// the top, the sign z < 0 and never a negative zero, and the bytes of the decimal text of z.  The
// script also checks that three mutated results fail the comparison, that the module releases
// every block it allocates, and writes the cases and the module's results for the comparison
// with the specification evaluated in native Lean (Native.lean).
// It also writes calls.txt, the same cases with each argument as the words that the module
// receives: a natural as its limbs, an integer as its sign and its limbs, a text as its words.
// Usage: node check.mjs bignum.wasm cases.txt module.txt [calls.txt]
import { writeFileSync } from 'node:fs';
import { load, Module, limbsOf, ofInt, textWords, wordsText, BASE } from './bignum.mjs';

const [wasmPath, casesPath, outPath, callsPath] = process.argv.slice(2);
const m = new Module(await load(wasmPath));

let seed = 0x2545f4914f6cdd1dn;
function next() {
  seed ^= seed << 13n; seed &= (1n << 64n) - 1n;
  seed ^= seed >> 7n;
  seed ^= seed << 17n; seed &= (1n << 64n) - 1n;
  return seed;
}
const rnd = (k) => Number(next() % BigInt(k));
function limb() {
  switch (rnd(8)) {
    case 0: return 0n;
    case 1: return BASE - 1n;
    case 2: return 1n;
    default: return next() % BASE;
  }
}
function natural(len) {
  let v = 0n;
  for (let i = 0; i < len; i++) v = v * BASE + limb();
  return v;
}
function naturalTop(len, top) { return top * BASE ** BigInt(len - 1) + natural(len - 1); }

const words = (x) => '[' + x.join(',') + ']';
const rec = (x) => (x.neg ? 1 : 0) + ':' + words(x.mag);
const sameNat = (limbs, n) => words(limbs) === words(limbsOf(n));
const sameInt = (x, z) => rec(x) === rec(ofInt(z));
const cmp = (a, b) => (a < b ? 0n : a === b ? 1n : 2n);
const tdiv = (a, b) => (b === 0n ? 0n : a / b);
const tmod = (a, b) => (b === 0n ? a : a % b);
function ediv(a, b) {
  if (b === 0n) return 0n;
  const q = a / b, r = a % b;
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q;
}
function emod(a, b) {
  if (b === 0n) return a;
  const r = a % b;
  return r < 0n ? r + (b < 0n ? -b : b) : r;
}

let passed = 0, failed = 0;
function check(ok, what) {
  if (ok) passed++; else { failed++; if (failed <= 20) console.log('FAIL ' + what); }
}

// Naturals.
const top = BASE - 1n;
const nats = [0n, 1n, 2n, 7n, 10n, top, BASE, BASE + 1n, BASE ** 2n - 1n, BASE ** 2n,
  BASE ** 2n + 1n, 10n ** 9n, 10n ** 9n - 1n, 10n ** 18n, 10n ** 19n, BASE ** 3n - 1n,
  BASE ** 8n - 1n, BASE ** 50n - 1n, BASE ** 60n, BASE ** 63n + 5n];
const divPairs = [
  [[5n, 6n], []], [[100n], [7n]], [[top, top], [3n]], [[1n, 2n, 3n], [top]], [[0n, 0n, 1n], [2n]],
  [[7n], [7n]], [[3n], [10n]], [[1n, 2n, 3n, 4n], [5n, 6n]], [[1n], [0n, 1n]], [[5n], [1n, 2n, 3n]],
  [[3n, 4n], [3n, 4n]], [[top, top, top, top, top, top], [top, top]],
  [[0n, 0n, 2147483648n, 2147483647n], [1n, 0n, 2147483648n]],
  [[3n, 0n, 2147483648n], [1n, 0n, 536870912n]], [[0n, 0n, 32768n, 32767n], [1n, 0n, 32768n]],
  [[0n, 4294967294n, 2147483648n], [4294967295n, 2147483648n]],
  [[0n, 4294967294n, 0n, 32768n], [65535n, 32768n]], [[0n, 1n, 2147483647n], [2147483647n, 2147483647n]],
  [[0n, 0n, 1n], [1n, 1n]]].map(([u, v]) => [valueOf(u), valueOf(v)]);
function valueOf(ls) { let v = 0n; for (let i = ls.length - 1; i >= 0; i--) v = v * BASE + ls[i]; return v; }
const pairs = [];
for (const a of nats) for (const b of nats) pairs.push([a, b]);
pairs.push(...divPairs);
for (let k = 0; k < 400; k++) pairs.push([natural(rnd(65)), natural(rnd(65))]);
for (let k = 0; k < 60; k++) pairs.push([natural(1 + rnd(64)), naturalTop(1 + rnd(8), 1n + BigInt(rnd(4)))]);
for (let k = 0; k < 40; k++) pairs.push([natural(1 + rnd(30)), natural(1)]);
for (let k = 0; k < 20; k++) pairs.push([natural(1 + rnd(10)), natural(11 + rnd(20))]);
for (const [la, lb] of [[1000, 1], [1000, 500], [2000, 999], [3000, 1500], [5000, 2500], [5000, 3],
  [4000, 4000], [1200, 2]]) pairs.push([natural(la), natural(lb)]);
for (let k = 0; k < 10; k++) { const a = natural(1 + rnd(40)); pairs.push([a, a]); }

const lines = [];
const results = [];
function record(op, args, out) { lines.push(op + '|' + args.join('|')); results.push(out); }

for (const [a, b] of pairs) {
  const u = limbsOf(a), v = limbsOf(b);
  const c = m.natCmp(u, v);
  check(c === cmp(a, b), `natCmp ${a} ${b}`);
  record('natCmp', [a, b], String(c));
  const s = m.natAdd(u, v);
  check(sameNat(s, a + b), `natAdd ${a} ${b}`);
  record('natAdd', [a, b], words(s));
  const d = m.natSub(u, v);
  check(d.lt === (a < b) && sameNat(d.mag, a < b ? b - a : a - b), `natSub ${a} ${b}`);
  record('natSub', [a, b], (d.lt ? 1 : 0) + ';' + words(d.mag));
  const p = m.natMul(u, v);
  check(sameNat(p, a * b), `natMul ${a} ${b}`);
  record('natMul', [a, b], words(p));
  const qr = m.natDivMod(u, v);
  if (b === 0n) check(qr.status === 1n && qr.q.length === 0 && qr.r.length === 0, `natDivMod ${a} 0`);
  else check(qr.status === 0n && sameNat(qr.q, a / b) && sameNat(qr.r, a % b), `natDivMod ${a} ${b}`);
  record('natDivMod', [a, b], qr.status + ';' + words(qr.q) + ';' + words(qr.r));
}

// natTrim on arrays with zero limbs at the top.
for (let k = 0; k < 40; k++) {
  const ws = limbsOf(natural(rnd(20)));
  for (let z = rnd(4); z > 0; z--) ws.push(0n);
  const t = m.natTrim(ws);
  check(sameNat(t, valueOf(ws)), `natTrim ${ws}`);
  lines.push('natTrim|' + ws.join(',')); results.push(words(t));
}

// Integers: every sign combination of the pairs that are not too long.
const ints = [];
for (const [a, b] of pairs.slice(0, 900)) for (const [sa, sb] of [[1n, 1n], [-1n, 1n], [1n, -1n], [-1n, -1n]]) ints.push([sa * a, sb * b]);
ints.push([-5n, 0n], [5n, 0n], [-7n, 2n], [7n, -2n], [-7n, -2n], [-6n, 2n], [6n, -3n], [-6n, -3n], [0n, -3n]);
for (const [a, b] of ints) {
  const x = ofInt(a), y = ofInt(b);
  const n = m.intNeg(x);
  check(sameInt(n, -a), `intNeg ${a}`);
  record('intNeg', [a], rec(n));
  const c = m.intCmp(x, y);
  check(c === cmp(a, b), `intCmp ${a} ${b}`);
  record('intCmp', [a, b], String(c));
  for (const [name, f] of [['intAdd', (p, q) => p + q], ['intSub', (p, q) => p - q], ['intMul', (p, q) => p * q]]) {
    const r = m.intBin(name, x, y);
    check(sameInt(r, f(a, b)), `${name} ${a} ${b}`);
    record(name, [a, b], rec(r));
  }
  for (const [name, fq, fr] of [['intTDivModChecked', tdiv, tmod], ['intEDivModChecked', ediv, emod]]) {
    const r = m.intDiv(name, x, y);
    if (b === 0n) check(r.status === 1n && sameInt(r.q, 0n) && sameInt(r.r, 0n), `${name} ${a} 0`);
    else check(r.status === 0n && sameInt(r.q, fq(a, b)) && sameInt(r.r, fr(a, b)), `${name} ${a} ${b}`);
    record(name, [a, b], r.status + ';' + rec(r.q) + ';' + rec(r.r));
  }
}

// Text: printing every integer of the cases, reading it back, and the text exports.
const textInts = [...new Set(ints.map(([a]) => a))];
for (const a of textInts) {
  const t = m.intToText(ofInt(a));
  check(wordsText(t) === a.toString(), `intToText ${a}`);
  record('intToText', [a], words(t));
  const back = m.intOfText(t);
  check(back.ok && sameInt(back.x, a), `intOfText ${a}`);
}
const rejected = ['', '-', '-0', '+1', '+0', '00', '007', '-007', '-01', ' 1', '1 ', '1\n', '\t1', '12a3',
  '--1', '1-', '.5', '1.0', '1e3', '0x10', '- 1'].map(textWords);
rejected.push([49n + 256n], [49n + (1n << 32n)], [49n + 128n], [45n + 128n, 49n], [49n, 50n + 256n],
  [(1n << 64n) - 1n], [49n, (1n << 63n) + 48n]);
const accepted = ['0', '7', '-7', '10', '-10', '4294967296', '-18446744073709551615',
  '1' + '0'.repeat(80), '-' + '9'.repeat(300)].map(textWords);
const texts = [...rejected, ...accepted, ...textInts.slice(0, 200).map((a) => textWords(a.toString()))];
function readText(ws) {
  const s = ws.every((w) => w < 256n) ? wordsText(ws) : null;
  return s !== null && /^(0|-?[1-9][0-9]*)$/.test(s) ? BigInt(s) : null;
}
for (const s of texts) {
  const r = m.intOfText(s);
  const z = readText(s);
  check(z === null ? !r.ok && sameInt(r.x, 0n) : r.ok && sameInt(r.x, z), `intOfText ${s}`);
  lines.push('intOfText|' + s.join(',')); results.push((r.ok ? 1 : 0) + ';' + rec(r.x));
  const n = m.textNeg(s);
  check(z === null ? n.status === 1n && n.text.length === 0
    : n.status === 0n && wordsText(n.text) === (-z).toString(), `textNeg ${s}`);
  lines.push('textNeg|' + s.join(',')); results.push(n.status + ';' + words(n.text));
}
const textOps = [['textAdd', false, (a, b) => a + b], ['textSub', false, (a, b) => a - b],
  ['textMul', false, (a, b) => a * b], ['textTDiv', true, tdiv], ['textTMod', true, tmod],
  ['textEDiv', true, ediv], ['textEMod', true, emod]];
const textPairs = [];
for (let k = 0; k < 300; k++) textPairs.push([texts[rnd(texts.length)], texts[rnd(texts.length)]]);
for (const a of accepted) for (const b of accepted) textPairs.push([a, b]);
for (const [s, t] of textPairs) {
  const za = readText(s), zb = readText(t);
  const status = za === null ? 1n : zb === null ? 2n : 0n;
  const c = m.textCmp(s, t);
  check(c.status === status && c.code === (status === 0n ? cmp(za, zb) : 0n), `textCmp ${s} ${t}`);
  lines.push('textCmp|' + s.join(',') + '|' + t.join(',')); results.push(c.status + ';' + c.code);
  for (const [name, division, f] of textOps) {
    const r = m.textBin(name, s, t);
    const st = status === 0n && division && zb === 0n ? 3n : status;
    check(r.status === st && (st === 0n ? wordsText(r.text) === f(za, zb).toString() : r.text.length === 0),
      `${name} ${s} ${t}`);
    lines.push(name + '|' + s.join(',') + '|' + t.join(',')); results.push(r.status + ';' + words(r.text));
  }
}

// Mutations that the comparison must reject.
const mutations = [];
{
  const d = m.natSub(limbsOf(BASE ** 2n), limbsOf(BASE ** 2n - 1n));
  mutations.push(['a trim that leaves one zero limb', sameNat(d.mag, 1n) && !sameNat([...d.mag, 0n], 1n)]);
  const z = m.intBin('intSub', ofInt(BASE + 5n), ofInt(BASE + 5n));
  mutations.push(['a sign left on zero', sameInt(z, 0n) && !sameInt({ neg: true, mag: z.mag }, 0n)]);
  const r = m.intDiv('intTDivModChecked', ofInt(-7n), ofInt(2n)).r;
  mutations.push(['a remainder with the divisor\'s sign', sameInt(r, -1n) && !sameInt({ neg: false, mag: r.mag }, -1n)]);
  const t = m.intToText(ofInt(0n));
  mutations.push(['a text of zero with a sign', wordsText(t) === '0' && '-0' !== (0n).toString()]);
}
for (const [what, ok] of mutations) check(ok, 'mutation: ' + what);

const allocs = m.x.allocCount.value, frees = m.x.freeCount.value;
check(allocs === frees, `allocations ${allocs} and releases ${frees}`);
writeFileSync(casesPath, lines.join('\n') + '\n');
// The words of each case's arguments, for the C host.
function callLine(line) {
  const [op, ...args] = line.split('|');
  if (op === 'natTrim' || op === 'intOfText' || op.startsWith('text')) return line;
  if (op.startsWith('nat')) return [op, ...args.map((a) => limbsOf(BigInt(a)).join(','))].join('|');
  return [op, ...args.flatMap((a) => { const x = ofInt(BigInt(a)); return [x.neg ? 1 : 0, x.mag.join(',')]; })].join('|');
}
if (callsPath) writeFileSync(callsPath, lines.map(callLine).join('\n') + '\n');
writeFileSync(outPath, results.join('\n') + '\n');
console.log(`bignum module against BigInt: ${passed} passed, ${failed} failed; ` +
  `${mutations.length} mutations rejected; ${allocs} allocations, ${frees} releases; ` +
  `${lines.length} cases written`);
if (failed > 0) process.exit(1);
