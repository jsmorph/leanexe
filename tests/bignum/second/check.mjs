// Compares the second iteration's exports with Node's BigInt, with no packages, and with the first
// iteration's natMul, intMul, and intOfText in the first iteration's module.  Usage:
//   node check.mjs bignum2.wasm bignum.wasm cases.txt module.txt
// The products are checked at the threshold of the library and at other thresholds through
// natMulKaraWith, on zero and one, all-ones limbs, operands at and around the threshold of 48
// limbs, operands of very different lengths, and random operands from 1 to 100,000 limbs; the
// readers on the texts of those numbers, texts of nines, texts around the bound of 768 chunks of
// the base elements, and texts outside the grammar.  It checks that the comparison rejects seeded
// wrong results, that each module releases every block it allocates, and it writes the cases up to
// 2,000 limbs and the second module's results on them for host/Native.lean.
import { writeFileSync } from 'node:fs';
import { load, Module, limbsOf, valueOf, textWords } from '../bignum.mjs';

const [path2, path1, casesPath, outPath] = process.argv.slice(2);
const x2 = await load(path2);
const x1 = await load(path1);
const M2 = new Module(x2);
const M1 = new Module(x1);

let seed = 0x2545f491;
function word() {
  seed ^= seed << 13; seed >>>= 0; seed ^= seed >>> 17; seed ^= seed << 5; seed >>>= 0;
  return seed;
}
function rnd(n) {
  const a = Array.from({ length: n }, () => BigInt(word()));
  if (n > 0 && a[n - 1] === 0n) a[n - 1] = 1n;
  return a;
}
const ones = (n) => Array(n).fill(0xFFFFFFFFn);
const same = (a, b) => a.length === b.length && a.every((w, i) => w === b[i]);
const recWords = (x) => [x.neg ? 1n : 0n, x.mag];

let passed = 0;
let failed = 0;
function expect(ok, what) {
  if (ok) passed++;
  else { failed++; if (failed <= 20) console.log('fail:', what); }
}

const cases = [];
const results = [];
const wordsS = (xs) => '[' + xs.join(',') + ']';
const MAXCASE = 2000;

function mulCase(u, v, compareFirst = true) {
  const want = limbsOf(valueOf(u) * valueOf(v));
  const got = M2.call('natMulKara', [u, v], ['array'])[0];
  expect(same(got, want), `natMulKara ${u.length}x${v.length}`);
  for (const t of [16n, 32n, 64n, 100n]) {
    if (u.length * v.length > 4e6 && t !== 16n) continue;
    const g = M2.call('natMulKaraWith', [t, u, v], ['array'])[0];
    expect(same(g, want), `natMulKaraWith ${t} ${u.length}x${v.length}`);
  }
  if (compareFirst) {
    const f = M1.call('natMul', [u, v], ['array'])[0];
    expect(same(got, f), `natMulKara = natMul ${u.length}x${v.length}`);
  }
  if (u.length <= MAXCASE && v.length <= MAXCASE) {
    cases.push(`natMul|${u.join(',')}|${v.join(',')}`);
    results.push(wordsS(got));
  }
}

function intMulCase(a, b, compareFirst = true) {
  const x = { neg: a < 0n, mag: limbsOf(a < 0n ? -a : a) };
  const y = { neg: b < 0n, mag: limbsOf(b < 0n ? -b : b) };
  const p = a * b;
  const [n, m] = M2.call('intMulKara', [...recWords(x), ...recWords(y)], ['word', 'array']);
  expect(n === (p < 0n ? 1n : 0n) && same(m, limbsOf(p < 0n ? -p : p)), `intMulKara ${a.toString().length}`);
  if (compareFirst) {
    const [n1, m1] = M1.call('intMul', [...recWords(x), ...recWords(y)], ['word', 'array']);
    expect(n1 === n && same(m1, m), 'intMulKara = intMul');
  }
  if (x.mag.length <= MAXCASE && y.mag.length <= MAXCASE) {
    cases.push(`intMul|${x.neg ? 1 : 0}:${x.mag.join(',')}|${y.neg ? 1 : 0}:${y.mag.join(',')}`);
    results.push(`${n}:${wordsS(m)}`);
  }
}

// The grammar of the readers, from Int64Text: "0" / ["-"] nonzero *digit for integers, and the
// same without the sign for naturals, over words that are byte values of ASCII digits.
const isNatText = (s) => /^(0|[1-9][0-9]*)$/.test(s);
const isIntText = (s) => /^(0|-?[1-9][0-9]*)$/.test(s);

function readCase(ws, compareFirst = true) {
  const s = ws.every((w) => w < 256n) ? Buffer.from(ws.map(Number)).toString('latin1') : null;
  const intOk = s !== null && isIntText(s);
  const natOk = s !== null && isNatText(s);
  const z = intOk ? BigInt(s) : 0n;
  const [f, n, m] = M2.call('intOfTextDC', [ws], ['word', 'word', 'array']);
  expect(f === (intOk ? 1n : 0n) && n === (z < 0n ? 1n : 0n) && same(m, limbsOf(z < 0n ? -z : z)),
    `intOfTextDC ${ws.length}`);
  const [fn, mn] = M2.call('natOfTextDC', [ws], ['word', 'array']);
  expect(fn === (natOk ? 1n : 0n) && same(mn, natOk ? limbsOf(z) : []), `natOfTextDC ${ws.length}`);
  for (const E of [1n, 16n, 64n]) {
    if (ws.length > 40000 && E !== 64n) continue;
    const [fe, me] = M2.call('natOfTextDCWith', [48n, E, ws], ['word', 'array']);
    expect(fe === fn && same(me, mn), `natOfTextDCWith ${E} ${ws.length}`);
  }
  if (compareFirst) {
    const [f1, n1, m1] = M1.call('intOfText', [ws], ['word', 'word', 'array']);
    expect(f1 === f && n1 === n && same(m1, m), `intOfTextDC = intOfText ${ws.length}`);
  }
  if (ws.length <= 9 * MAXCASE) {
    cases.push(`read|${ws.join(',')}`);
    results.push(`${f}:${n}:${wordsS(m)};${fn}:${wordsS(mn)}`);
  }
}

// products: zero, one, all-ones limbs, the threshold, different lengths, random lengths
const small = [[], [1n], [2n], [0xFFFFFFFFn], [0n, 1n], ones(3)];
for (const u of small) for (const v of small) mulCase(u, v);
for (const n of [1, 2, 15, 16, 17, 47, 48, 49, 95, 96, 97, 191, 192, 193, 500, 1000, 4096, 5000]) {
  mulCase(ones(n), ones(n));
  mulCase(ones(n), rnd(n));
}
for (const m of [46, 47, 48, 49, 50, 94, 95, 96, 97, 98]) {
  for (const n of [46, 47, 48, 49, 50, 94, 95, 96, 97, 98]) mulCase(rnd(m), rnd(n));
}
for (const [m, n] of [[1, 10000], [10000, 1], [47, 10000], [48, 10000], [49, 10001], [10000, 96],
  [3, 100000], [100, 100000], [5000, 48], [1000, 999], [1001, 1000], [2049, 2048], [4097, 64],
  [96, 4999], [48, 100], [100, 48], [1, 1], [2000, 3]]) {
  mulCase(rnd(m), rnd(n), m * n <= 2e7);
}
for (let r = 0; r < 300; r++) {
  const m = Math.floor(Math.exp(Math.log(2000) * (word() / 2 ** 32))) + 1;
  const n = Math.floor(Math.exp(Math.log(2000) * (word() / 2 ** 32))) + 1;
  mulCase(rnd(m), rnd(n));
}
for (const n of [10000, 30000, 100000]) mulCase(rnd(n), rnd(n), n <= 30000);
mulCase(ones(100000), ones(100000), false);

// integer products: every sign combination on a sample of the pairs above
const signed = [0n, 1n, -1n, 2n ** 32n - 1n, -(2n ** 64n), valueOf(rnd(48)), valueOf(rnd(97)),
  valueOf(ones(500)), valueOf(rnd(1500))];
for (const a of signed) for (const b of signed) for (const sa of [1n, -1n]) for (const sb of [1n, -1n]) {
  intMulCase(sa * a, sb * b);
}

// readers
const digits = (k) => { let s = String(1 + (word() % 9)); for (let i = 1; i < k; i++) s += String(word() % 10); return s; };
for (const s of ['0', '1', '9', '10', '-1', '-9', '-10', '123456789', '1234567890', '999999999',
  '1000000000', '-1000000000']) readCase(textWords(s));
for (const k of [1, 8, 9, 10, 17, 18, 19, 80, 81, 82, 300, 1000, 6911, 6912, 6913, 13823, 13824,
  13825, 20000, 30000]) {
  for (const s of [digits(k), '9'.repeat(k), '1' + '0'.repeat(k - 1)]) {
    readCase(textWords(s));
    readCase(textWords('-' + s));
  }
}
for (const n of [1, 2, 47, 48, 49, 100, 768, 769, 1000, 5000]) {
  readCase(textWords(valueOf(rnd(n)).toString()));
  readCase(textWords('-' + valueOf(ones(n)).toString()));
}
for (const n of [10000, 30000]) readCase(textWords(valueOf(rnd(n)).toString()), n <= 10000);
readCase(textWords(valueOf(rnd(100000)).toString()), false);
for (const bad of ['', '-', '-0', '+1', '007', '00', '-01', ' 1', '1 ', '1e3', '12a3', '--1',
  '1-', '٣', '0x10']) readCase(textWords(bad));
for (const ws of [[256n + 49n], [49n, 48n + 256n], [2n ** 32n + 49n], [45n, 49n + 256n], [128n + 49n],
  [48n, 48n], [0n]]) readCase(ws);

// the comparison rejects seeded wrong results
let rejected = 0;
{
  const want = limbsOf(valueOf(rnd(60)) * 3n);
  const wrong = [...want]; wrong[0] ^= 1n;
  if (!same(wrong, want)) rejected++;
  if (!same([...want, 0n], want)) rejected++;
  const s = '-0';
  if (!isIntText(s)) rejected++;
  const neg0 = { neg: true, mag: [] };
  if (!(neg0.neg === false && same(neg0.mag, []))) rejected++;
}

writeFileSync(casesPath, cases.join('\n') + '\n');
writeFileSync(outPath, results.join('\n') + '\n');
const alloc2 = x2.allocCount.value, free2 = x2.freeCount.value;
const alloc1 = x1.allocCount.value, free1 = x1.freeCount.value;
expect(alloc2 === free2, 'second module releases every block');
expect(alloc1 === free1, 'first module releases every block');
console.log(`second bignum module against BigInt and the first module: ${passed} passed, ${failed} failed; ` +
  `${rejected} seeded wrong results rejected; ${alloc2} allocations, ${free2} releases; ${cases.length} cases written`);
if (failed > 0) process.exit(1);
