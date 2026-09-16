#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const max = 18446744073709551615n;
const cases = [
  ["Prop", [0,0,0], [], 0,10, [0,1,0,0,0,0,1,0]],
  ["A x context", [0,1,0,1,0,0], [0,1], 1,20, [0,3,0,1,0,1,0,0,0,2,0,1,1,0]],
  ["older lookup", [0,1,0,1,0,0,1,1,0], [0,1], 2,20,
    [0,0,0,1,0,1,0,0,1,1,0,0,2,0]],
  ["free", [1,0,0], [], 0,20,[1]],
  ["out of scope", [0,1,0,1,1,0], [0], 1,20,[1]],
  ["huge index", [0,1,0,1,max,0], [0], 1,20,[1]],
  ["unbound assumption", [1,0,0], [0], 0,20,[1]],
  ["proof is not a type", [0,0,0,1,0,0], [0,1,1], 1,20,[1]],
  ["bad context id", [0,0,0], [1], 0,20,[4]],
  ["unsupported Pi", [0,0,0,2,0,0], [], 1,20,[3]],
  ["overflow", [0,max,0], [], 0,20,[2]],
  ["exhausted during context", [0,1,0,1,0,0], [0,1], 1,2,[5]],
  ["no fuel", [0,0,0], [], 0,0,[5]],
  ["malformed", [3,0,0], [], 0,20,[4]],
];
const artifact = compile("Infer", "inferOpen", "m0-4");
const native = reference("Infer", cases.map(([,g,c,r,f]) => `inferOpen ${leanArray(g)} ${leanArray(c)} ${r} ${f}`));
const words = text => [...text.matchAll(/\d+/g)].map(m => BigInt(m[0]));
for (const [i,[name,g,c,r,f,expected]] of cases.entries()) {
  assert.deepEqual(words(native[i]), expected.map(BigInt), `Lean: ${name}`);
  const actual = host.call(artifact,"inferOpen","array-u64",[host.arrayU64(g),host.arrayU64(c),host.i64(r),host.i64(f)]);
  assert.deepEqual(words(actual), expected.map(BigInt), `WASM: ${name}`);
}
console.log(`checked ${cases.length} M0.4 WASM/standard-Lean open judgments; artifact: ${artifact}`);
