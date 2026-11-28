// Compares the third iteration's exports with Node's BigInt, with no packages, and with the first
// iteration's natDivModChecked, intTDivModChecked, intEDivModChecked, and intToText in the first
// iteration's module.  Usage:
//   node check.mjs bignum3.wasm bignum.wasm cases.txt module.txt
// The divisions are checked at the library's thresholds and at other thresholds through
// natDivModCheckedBZWith, on zero, one, and a zero divisor, divisors with a top limb of 1, all-ones
// limbs, lengths at and around the thresholds of 32 quotient limbs and 192 limbs, dividends much
// longer than the divisor and of its length, and random operands up to 200,000 by 100,000 limbs;
// the printers on the same numbers, on powers of ten around the powers 10^(9·2^i) that the printer
// divides by, on lengths around the thresholds of the printer, and on random numbers up to 100,000
// limbs, with both signs.  It checks that the comparison rejects seeded wrong results, that each
// module releases every block it allocates, and it writes the cases up to 2,000 limbs and the
// third module's results on them for host/Native.lean.
import { writeFileSync } from 'node:fs';
import { load, Module, limbsOf, valueOf, wordsText } from '../bignum.mjs';

const [path3, path1, casesPath, outPath] = process.argv.slice(2);
const x3 = await load(path3);
const x1 = await load(path1);
const M3 = new Module(x3);
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
const topOne = (n) => (n === 0 ? [] : [...rnd(n - 1), 1n]);
const same = (a, b) => a.length === b.length && a.every((w, i) => w === b[i]);
const recWords = (x) => [x.neg ? 1n : 0n, x.mag];
const ofInt = (z) => ({ neg: z < 0n, mag: limbsOf(z < 0n ? -z : z) });

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

const tdiv = (a, b) => (b === 0n ? 0n : a / b);
const tmod = (a, b) => (b === 0n ? a : a % b);
const ediv = (a, b) => {
  if (b === 0n) return 0n;
  const q = a / b, r = a % b;
  return r < 0n ? (b > 0n ? q - 1n : q + 1n) : q;
};
const emod = (a, b) => {
  if (b === 0n) return a;
  const r = a % b;
  return r < 0n ? (b > 0n ? r + b : r - b) : r;
};

function natDivCase(u, v, compareFirst = true, withs = true) {
  const a = valueOf(u), b = valueOf(v);
  const [st, q, r] = M3.call('natDivModCheckedBZ', [u, v], ['word', 'array', 'array']);
  const ok = b === 0n ? st === 1n && q.length === 0 && r.length === 0
    : st === 0n && same(q, limbsOf(a / b)) && same(r, limbsOf(a % b));
  expect(ok, `natDivModCheckedBZ ${u.length}/${v.length}`);
  if (withs) {
    for (const [t, T, D] of [[48n, 3n, 2n], [16n, 8n, 8n], [48n, 32n, 32n], [48n, 100n, 2n]]) {
      if (u.length > 20000 && T !== 32n) continue;
      const [s2, q2, r2] = M3.call('natDivModCheckedBZWith', [t, T, D, u, v],
        ['word', 'array', 'array']);
      expect(s2 === st && same(q2, q) && same(r2, r), `natDivModCheckedBZWith ${T} ${D} ${u.length}/${v.length}`);
    }
  }
  if (compareFirst) {
    const [s1, q1, r1] = M1.call('natDivModChecked', [u, v], ['word', 'array', 'array']);
    expect(s1 === st && same(q1, q) && same(r1, r), `= natDivModChecked ${u.length}/${v.length}`);
  }
  if (u.length <= MAXCASE && v.length <= MAXCASE) {
    cases.push(`natDiv|${u.join(',')}|${v.join(',')}`);
    results.push(`${st}:${wordsS(q)}:${wordsS(r)}`);
  }
}

function intDivCase(a, b, compareFirst = true) {
  const x = ofInt(a), y = ofInt(b);
  const args = [...recWords(x), ...recWords(y)];
  const shape = ['word', 'word', 'array', 'word', 'array'];
  const outs = [];
  for (const [name, fq, fr, first] of [['intTDivModCheckedBZ', tdiv, tmod, 'intTDivModChecked'],
    ['intEDivModCheckedBZ', ediv, emod, 'intEDivModChecked']]) {
    const [st, qn, qm, rn, rm] = M3.call(name, args, shape);
    const q = ofInt(fq(a, b)), r = ofInt(fr(a, b));
    const ok = b === 0n ? st === 1n && qn === 0n && qm.length === 0 && rn === 0n && rm.length === 0
      : st === 0n && qn === (q.neg ? 1n : 0n) && same(qm, q.mag) && rn === (r.neg ? 1n : 0n) &&
        same(rm, r.mag);
    expect(ok, `${name} ${a.toString().length}/${b.toString().length}`);
    if (compareFirst) {
      const g = M1.call(first, args, shape);
      expect(g[0] === st && g[1] === qn && same(g[2], qm) && g[3] === rn && same(g[4], rm),
        `${name} = ${first}`);
    }
    outs.push(`${st}:${qn}:${wordsS(qm)}:${rn}:${wordsS(rm)}`);
  }
  if (x.mag.length <= MAXCASE && y.mag.length <= MAXCASE) {
    cases.push(`intDiv|${x.neg ? 1 : 0}:${x.mag.join(',')}|${y.neg ? 1 : 0}:${y.mag.join(',')}`);
    results.push(outs.join(';'));
  }
}

function printCase(u, compareFirst = true, withs = true) {
  const a = valueOf(u);
  const t = M3.call('natToTextDC', [u], ['array'])[0];
  expect(wordsText(t) === a.toString(), `natToTextDC ${u.length}`);
  const tp = M3.call('intToTextDC', recWords({ neg: false, mag: u }), ['array'])[0];
  expect(same(tp, t), `intToTextDC + ${u.length}`);
  const tn = M3.call('intToTextDC', recWords({ neg: u.length > 0, mag: u }), ['array'])[0];
  expect(wordsText(tn) === (-a).toString(), `intToTextDC - ${u.length}`);
  if (withs) {
    for (const [L, P] of [[0n, 0n], [1n, 0n], [3n, 2n], [5n, 32n], [8n, 0n]]) {
      if (u.length > 20000 && L !== 5n) continue;
      const tw = M3.call('natToTextDCWith', [48n, 32n, L, P, u], ['array'])[0];
      expect(same(tw, t), `natToTextDCWith ${L} ${P} ${u.length}`);
    }
  }
  if (compareFirst) {
    const t1 = M1.call('intToText', recWords({ neg: u.length > 0, mag: u }), ['array'])[0];
    expect(same(t1, tn), `intToTextDC = intToText ${u.length}`);
  }
  if (u.length <= MAXCASE) {
    cases.push(`print|${u.join(',')}`);
    results.push(`${wordsS(t)};${wordsS(tn)}`);
  }
}

// divisions: zero, one, a zero divisor, small values
const small = [[], [1n], [2n], [0xFFFFFFFFn], [0n, 1n], ones(3), [5n, 1n]];
for (const u of small) for (const v of small) natDivCase(u, v);
// around the thresholds: divisors of 190 to 194 limbs, quotients around 32, 64, and 192 limbs
for (const n of [190, 191, 192, 193, 194]) {
  for (const m of [0, 1, 2, 31, 32, 33, 62, 63, 64, 65, 66, 190, 191, 192, 193, 194, n + 1]) {
    natDivCase(rnd(n + m), rnd(n), true, m % 31 === 1);
  }
}
for (const n of [30, 31, 32, 33, 34, 62, 63, 64, 65, 66, 96, 128, 383, 384, 385]) {
  natDivCase(rnd(2 * n), rnd(n));
  natDivCase(rnd(2 * n + 1), topOne(n));
}
// divisors with a top limb of 1, all-ones limbs, equal lengths
for (const n of [2, 3, 50, 192, 193, 300, 1000, 2000]) {
  natDivCase(rnd(2 * n), topOne(n));
  natDivCase(ones(2 * n), ones(n));
  natDivCase(ones(n), ones(n));
  natDivCase(rnd(n), rnd(n));
  natDivCase(ones(n + 1), topOne(n));
  natDivCase(rnd(n + 1), rnd(n));
}
// dividends much longer than the divisor, and quotients shorter than the divisor
for (const [m, n] of [[100000, 10], [100000, 200], [50000, 192], [50000, 193], [20000, 1000],
  [10000, 3], [6000, 2000], [3000, 2000], [2500, 2000], [2200, 2000], [2100, 2000], [10000, 9000],
  [30000, 20000], [4000, 64]]) {
  natDivCase(rnd(m), rnd(n), m <= 20000, m <= 20000);
}
for (let r = 0; r < 300; r++) {
  const m = Math.floor(Math.exp(Math.log(2000) * (word() / 2 ** 32)));
  const n = Math.floor(Math.exp(Math.log(2000) * (word() / 2 ** 32))) + 1;
  natDivCase(rnd(m), rnd(n));
}
for (const n of [10000, 30000, 100000]) {
  natDivCase(rnd(2 * n), rnd(n), n <= 10000, false);
  natDivCase(rnd(n + n / 2), rnd(n), false, false);
}
natDivCase(ones(200000), ones(100000), false, false);
natDivCase(rnd(200000), topOne(100000), false, false);

// integer divisions: every sign combination on a sample of values, zero divisors included
const signed = [0n, 1n, 2n ** 32n - 1n, 2n ** 64n, 7n, valueOf(rnd(5)), valueOf(rnd(200)),
  valueOf(rnd(400)), valueOf(ones(193)), valueOf(topOne(250))];
for (const a of signed) for (const b of signed) for (const sa of [1n, -1n]) for (const sb of [1n, -1n]) {
  intDivCase(sa * a, sb * b);
}
intDivCase(valueOf(rnd(5000)), -valueOf(rnd(2400)));
intDivCase(-valueOf(rnd(5000)), valueOf(rnd(2400)));

// printers
for (const u of [[], [1n], [9n], [10n], [999999999n], [1000000000n], [0xFFFFFFFFn], ones(2),
  ones(3)]) printCase(u);
for (const n of [1, 2, 29, 30, 31, 32, 33, 34, 59, 60, 61, 119, 120, 121, 239, 240, 241, 500, 1000,
  2000]) {
  printCase(rnd(n));
  printCase(ones(n));
}
for (const i of [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]) {
  const p = 10n ** BigInt(9 * 2 ** i);
  for (const z of [p - 1n, p, p + 1n, p * p - 1n, p * p, p * (p - 1n)]) {
    printCase(limbsOf(z), z < 10n ** 30000n, z < 10n ** 30000n);
  }
}
for (let r = 0; r < 100; r++) {
  printCase(rnd(Math.floor(Math.exp(Math.log(2000) * (word() / 2 ** 32))) + 1));
}
for (const n of [5000, 10000, 30000, 100000]) printCase(rnd(n), n <= 10000, n <= 30000);
printCase(ones(100000), false, false);

// the comparison rejects seeded wrong results
let rejected = 0;
{
  const a = valueOf(rnd(300)), b = valueOf(rnd(200));
  const q = limbsOf(a / b);
  const wrong = [...q]; wrong[0] ^= 1n;
  if (!same(wrong, q)) rejected++;
  if (!same([...q, 0n], q)) rejected++;
  if (('0' + a.toString()) !== a.toString()) rejected++;
  const r = limbsOf(a % b);
  if (!same(limbsOf(valueOf(r) + b), r)) rejected++;
}

writeFileSync(casesPath, cases.join('\n') + '\n');
writeFileSync(outPath, results.join('\n') + '\n');
const alloc3 = x3.allocCount.value, free3 = x3.freeCount.value;
const alloc1 = x1.allocCount.value, free1 = x1.freeCount.value;
expect(alloc3 === free3, 'third module releases every block');
expect(alloc1 === free1, 'first module releases every block');
console.log(`third bignum module against BigInt and the first module: ${passed} passed, ${failed} failed; ` +
  `${rejected} seeded wrong results rejected; ${alloc3} allocations, ${free3} releases; ${cases.length} cases written`);
if (failed > 0) process.exit(1);
