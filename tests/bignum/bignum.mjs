// Calls the exports of the module of Library.Numerics.Bignum.Compiled from JavaScript BigInt values.
// An array argument is allocated through the module's alloc as a length word followed by its
// words, a BigInt record is passed as its sign word and its magnitude's pointer, and every array
// the host allocates or receives is released after the call, so the heap returns to its state.
import { readFileSync } from 'node:fs';

export const BASE = 1n << 32n;

export async function load(path) {
  const { instance } = await WebAssembly.instantiate(readFileSync(path));
  return instance.exports;
}

/** The canonical limbs of a natural: base-2^32 digits, least significant first. */
export function limbsOf(n) {
  if (n < 0n) throw new Error('limbsOf of a negative value');
  const out = [];
  while (n > 0n) { out.push(n % BASE); n /= BASE; }
  return out;
}

export function valueOf(limbs) {
  let v = 0n;
  for (let i = limbs.length - 1; i >= 0; i--) v = v * BASE + limbs[i];
  return v;
}

/** The canonical integer of z: the sign z < 0 and the limbs of |z|. */
export function ofInt(z) { return { neg: z < 0n, mag: limbsOf(z < 0n ? -z : z) }; }

export function toInt(x) { const v = valueOf(x.mag); return x.neg ? -v : v; }

export function textWords(s) { return Array.from(Buffer.from(s, 'latin1'), (b) => BigInt(b)); }

export function wordsText(ws) { return Buffer.from(ws.map((w) => Number(w))).toString('latin1'); }

export class Module {
  constructor(exports) { this.x = exports; }

  put(words) {
    const p = this.x.alloc(BigInt(8 + 8 * words.length));
    const view = new DataView(this.x.memory.buffer);
    const base = Number(p);
    view.setBigUint64(base, BigInt(words.length), true);
    words.forEach((w, i) => view.setBigUint64(base + 8 + 8 * i, w, true));
    return p;
  }

  take(p) {
    const view = new DataView(this.x.memory.buffer);
    const base = Number(p);
    const n = Number(view.getBigUint64(base, true));
    const out = new Array(n);
    for (let i = 0; i < n; i++) out[i] = view.getBigUint64(base + 8 + 8 * i, true);
    this.x.release(p);
    return out;
  }

  /** Calls `name` on arrays given as word lists and scalars given as BigInts, in order. */
  call(name, args, shape) {
    const owned = [];
    const raw = args.map((a) => {
      if (Array.isArray(a)) { const p = this.put(a); owned.push(p); return p; }
      return a;
    });
    let res = this.x[name](...raw);
    for (const p of owned) this.x.release(p);
    if (!Array.isArray(res)) res = [res];
    return shape.map((kind, i) => (kind === 'array' ? this.take(res[i]) : res[i]));
  }

  rec(x) { return [x.neg ? 1n : 0n, x.mag]; }

  natTrim(u) { return this.call('natTrim', [u], ['array'])[0]; }
  natCmp(u, v) { return this.call('natCmp', [u, v], ['word'])[0]; }
  natAdd(u, v) { return this.call('natAdd', [u, v], ['array'])[0]; }
  natSub(u, v) { const [f, d] = this.call('natSub', [u, v], ['word', 'array']); return { lt: f === 1n, mag: d }; }
  natMul(u, v) { return this.call('natMul', [u, v], ['array'])[0]; }
  natDivMod(u, v) {
    const [st, q, r] = this.call('natDivModChecked', [u, v], ['word', 'array', 'array']);
    return { status: st, q, r };
  }
  intNeg(x) { const [n, m] = this.call('intNeg', this.rec(x), ['word', 'array']); return { neg: n === 1n, mag: m }; }
  intCmp(x, y) { return this.call('intCmp', [...this.rec(x), ...this.rec(y)], ['word'])[0]; }
  intBin(name, x, y) {
    const [n, m] = this.call(name, [...this.rec(x), ...this.rec(y)], ['word', 'array']);
    return { neg: n === 1n, mag: m };
  }
  intDiv(name, x, y) {
    const [st, n1, m1, n2, m2] = this.call(name, [...this.rec(x), ...this.rec(y)],
      ['word', 'word', 'array', 'word', 'array']);
    return { status: st, q: { neg: n1 === 1n, mag: m1 }, r: { neg: n2 === 1n, mag: m2 } };
  }
  intToText(x) { return this.call('intToText', this.rec(x), ['array'])[0]; }
  intOfText(s) {
    const [f, n, m] = this.call('intOfText', [s], ['word', 'word', 'array']);
    return { ok: f === 1n, x: { neg: n === 1n, mag: m } };
  }
  textNeg(s) { const [st, t] = this.call('textNeg', [s], ['word', 'array']); return { status: st, text: t }; }
  textCmp(s, t) { const [st, c] = this.call('textCmp', [s, t], ['word', 'word']); return { status: st, code: c }; }
  textBin(name, s, t) { const [st, r] = this.call(name, [s, t], ['word', 'array']); return { status: st, text: r }; }
}
