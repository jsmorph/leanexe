// Minimal host bridge for leanexe word arrays. VM objects stay inside the arena.
export class Host {
  constructor(x) { this.x = x; }
  array(words) {
    const ptr = this.x.alloc(BigInt(8 * (words.length + 1)));
    const view = new DataView(this.x.memory.buffer), base = Number(ptr);
    view.setBigUint64(base - 24, 2n, true); // Array of words: no owned child pointers.
    view.setBigUint64(base - 16, 1n, true);
    view.setBigUint64(base - 8, 0n, true);
    view.setBigUint64(base, BigInt(words.length), true);
    words.forEach((word, i) => view.setBigUint64(base + 8 * (i + 1), BigInt(word), true));
    return ptr;
  }
  words(ptr) {
    const v = new DataView(this.x.memory.buffer), base = Number(ptr);
    return Array.from({length: Number(v.getBigUint64(base, true))}, (_, i) =>
      v.getBigUint64(base + 8 * (i + 1), true));
  }
  release(ptr) { this.x.release(ptr); }
  outstanding() { return this.x.allocCount.value - this.x.freeCount.value; }
}

export const cell = (s, h, f) => s[24 + 5 * (Number(h) - 1) + f];
