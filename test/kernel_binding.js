#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const max = 18446744073709551615n;
const scope = [
  ["free", [1,0,0], 0,0,10,1],
  ["nearest", [1,0,0], 0,1,10,0],
  ["outer", [1,1,0], 0,1,10,1],
  ["lambda body", [0,0,0,1,0,0,3,0,1], 2,0,3,0],
  ["Pi body", [0,0,0,1,0,0,2,0,1], 2,0,3,0],
  ["domain not bound", [1,0,0,3,0,0], 1,0,10,1],
  ["shared in domain and body", [1,0,0,2,0,0], 1,1,3,0],
  ["nested outer variable", [0,0,0,1,1,0,3,0,1,3,0,2], 3,0,5,0],
  ["outside nested", [0,0,0,1,2,0,3,0,1,3,0,2], 3,0,8,1],
  ["fuel", [0,0,0,1,0,0,3,0,1], 2,0,2,5],
  ["depth overflow", [0,0,0,2,0,0], 1,max,10,2],
  ["max index", [1,max,0], 0,max,10,1],
  ["malformed", [2,0,0], 0,0,10,4],
];
let artifact = compile("Binding", "checkScope", "m0-3-scope");
let native = reference("Binding", scope.map(([,g,r,d,f]) => `(checkScope ${leanArray(g)} ${r} ${d} ${f}).toNat`));
for (const [i,[name,g,r,d,f,expected]] of scope.entries()) {
  assert.equal(BigInt(native[i]), BigInt(expected), `Lean: ${name}`);
  assert.equal(host.callI64(artifact,"checkScope",[host.arrayU64(g),...[r,d,f].map(host.i64)]),BigInt(expected),`WASM: ${name}`);
}
const nested = [0,0,0,1,0,0,1,1,0,2,1,2,3,0,3];
const shifts = [
  ["free", [1,0,0], 0,0,1,10, [0,1,1,0,0,1,1,0]],
  ["below cutoff", [1,0,0], 0,1,7,1, [0,0,1,0,0]],
  ["at cutoff", [1,1,0], 0,1,7,1, [0,1,1,1,0,1,8,0]],
  ["under binder", [0,0,0,1,1,0,3,0,1], 2,0,2,4,
    [0,4,0,0,0,1,1,0,3,0,1,1,3,0,3,0,3]],
  ["bound preserved", [0,0,0,1,0,0,3,0,1], 2,0,2,4,
    [0,3,0,0,0,1,0,0,3,0,1,3,0,1]],
  ["nested binders", nested, 4,0,3,20, [0,6,...nested,2,1,2,3,0,5]],
  ["shared cutoff differs", [1,0,0,2,0,0], 1,0,1,4,
    [0,3,1,0,0,2,0,0,1,1,0,2,2,0]],
  ["overflow", [1,max,0], 0,0,1,10,[2]],
  ["max unchanged", [1,max,0], 0,0,0,1,[0,0,1,max,0]],
  ["cutoff overflow", [0,0,0,2,0,0], 1,max,1,10,[2]],
  ["exhausted", [0,0,0,2,0,0], 1,0,1,3,[5]],
  ["malformed", [1,0], 0,0,1,10,[4]],
];
artifact = compile("Binding", "shiftGraph", "m0-3-shift");
native = reference("Binding", shifts.map(([,g,r,c,d,f]) => `shiftGraph ${leanArray(g)} ${r} ${c} ${d} ${f}`));
// Parse decimal words as BigInt: JSON.parse would round UInt64 boundaries.
const words = text => [...text.matchAll(/\d+/g)].map(m => BigInt(m[0]));
for (const [i,[name,g,r,c,d,f,expected]] of shifts.entries()) {
  assert.deepEqual(words(native[i]), expected.map(BigInt), `Lean: ${name}`);
  const actual = host.call(artifact,"shiftGraph","array-u64",[host.arrayU64(g),...[r,c,d,f].map(host.i64)]);
  assert.deepEqual(words(actual), expected.map(BigInt), `WASM: ${name}`);
}
console.log(`checked ${scope.length} scope and ${shifts.length} exact shift results in WASM/standard Lean; artifacts: m0-3-scope, m0-3-shift`);
