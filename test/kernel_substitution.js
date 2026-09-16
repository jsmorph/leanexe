#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const max = 18446744073709551615n;
const capture = [0,0,0,1,0,0,1,1,0,3,0,2];
const nested = [0,0,0,1,0,0,1,2,0,3,0,2,3,0,3];
const cases = [
  ["replace", [0,0,0,1,0,0],1,0,10,[0,0,0,0,0,1,0,0]],
  ["index adjustment",[1,1,0,0,0,0],0,1,10,[0,2,1,1,0,0,0,0,1,0,0]],
  ["unused",[0,7,0,1,0,0],0,1,1,[0,0,0,7,0,1,0,0]],
  ["avoid capture",capture,3,1,10,[0,5,...capture,1,1,0,3,0,4]],
  ["nested lifting",nested,4,1,20,[0,7,...nested,1,2,0,3,0,5,3,0,6]],
  ["preserve inner bound variable",[0,0,0,1,0,0,3,0,1],2,0,10,
    [0,3,0,0,0,1,0,0,3,0,1,3,0,1]],
  ["substitute in domain only",[1,0,0,0,2,0,2,0,0],2,1,10,
    [0,3,1,0,0,0,2,0,2,0,0,2,1,0]],
  ["max decrement",[1,max,0,0,0,0],0,1,10,[0,2,1,max,0,0,0,0,1,max-1n,0]],
  ["replacement shift overflow",[0,0,0,1,1,0,3,0,1,1,max,0],2,3,20,[2]],
  ["shared fuel exhaustion",capture,3,1,4,[5]],
  ["bad argument",[0,0,0],0,1,10,[4]],
  ["malformed",[2,0,0],0,0,10,[4]],
];
const artifact = compile("Substitution","instantiateGraph","m0-7");
const native = reference("Substitution", cases.map(([,g,r,a,f]) => `instantiateGraph ${leanArray(g)} ${r} ${a} ${f}`));
const words = text => [...text.matchAll(/\d+/g)].map(m => BigInt(m[0]));
for (const [i,[name,g,r,a,f,expected]] of cases.entries()) {
  assert.deepEqual(words(native[i]), expected.map(BigInt), `Lean: ${name}`);
  const actual = host.call(artifact,"instantiateGraph","array-u64",[host.arrayU64(g),...[r,a,f].map(host.i64)]);
  assert.deepEqual(words(actual), expected.map(BigInt), `WASM: ${name}`);
}
console.log(`checked ${cases.length} exact M0.7 substitution outputs in WASM/standard Lean; artifact: ${artifact}`);
