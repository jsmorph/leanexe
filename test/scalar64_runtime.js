'use strict';
// Runtime compliance smoke tests. The Lean theorems quantify over every input.
const fs = require('fs');
const path = require('path');
const root = process.argv[2];
const u = x => BigInt.asUintN(64, x);
const values = [0n, 1n, 2n, 42n, 63n, 64n, 65n, (1n << 63n), (1n << 64n) - 1n];
const expected = {
  affine: (x, y) => u(3n * x + 2n * y + 7n),
  choose: (x, y) => u(x === 0n ? y + 1n : x + y),
  mix: x => {
    let z = u((x ^ (x >> 30n)) * 0xbf58476d1ce4e5b9n);
    z = u((z ^ (z >> 27n)) * 0x94d049bb133111ebn);
    return u(z ^ (z >> 31n));
  },
  helper: (x, y) => u(u(x + 1n) * 5n + u(y * 2n) + x),
  gcd: (x, y) => { while (y !== 0n) [x, y] = [y, x % y]; return x; },
};
let count = 0;
for (const [name, source] of Object.entries(expected)) {
  const bytes = fs.readFileSync(path.join(root, name, 'program.wasm'));
  if (!WebAssembly.validate(bytes)) throw new Error(`${name}: engine rejected bytes`);
  const module = new WebAssembly.Module(bytes);
  if (WebAssembly.Module.imports(module).length) throw new Error(`${name}: unexpected imports`);
  const instance = new WebAssembly.Instance(module);
  const exported = Object.keys(instance.exports);
  if (exported.length !== 1 || exported[0] !== name) throw new Error(`${name}: wrong exports`);
  for (const x of values) {
    for (const y of (name === 'mix' ? [0n] : values)) {
      const args = name === 'mix' ? [x] : [x, y];
      if (u(instance.exports[name](...args)) !== source(...args))
        throw new Error(`${name}: mismatch at ${args}`);
      count++;
    }
  }
}
console.log(`WASM engine smoke tests passed: ${count} cases`);
