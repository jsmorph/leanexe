#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const identity = [0,0,0,1,0,0,1,1,0,2,1,2,2,0,3];
const typeIdentity = [...identity]; typeIdentity[1] = 1;
const cases = [
  ["implication identity type", identity, [],4,100,0,0],
  ["Type identity type", typeIdentity, [],4,100,0,2],
  ["Prop to Prop", [0,0,0,2,0,0], [],1,100,0,1],
  ["large impredicative domain", [0,0,0,0,100,0,1,1,0,2,1,2], [0],3,100,0,0],
  ["Pi local assumption", [0,0,0,2,0,0,1,0,0], [1],2,100,0,"Pi"],
  ["body is proof", [0,0,0,1,0,0,2,1,1,2,0,2], [],3,100,1],
  ["domain is proof", [0,0,0,1,0,0,2,1,0], [0,1],2,100,1],
  ["body uses wrong scope", [0,0,0,1,1,0,2,0,1], [],2,100,1],
  ["fuel exhausted", identity, [],4,1,5],
  ["universe overflow", [0,18446744073709551615n,0,2,0,0], [],1,100,2],
];
const artifact = compile("Pi", "inferPi", "m0-5");
const native = reference("Pi", cases.map(([,g,c,r,f]) => `inferPi ${leanArray(g)} ${leanArray(c)} ${r} ${f}`));
const words = text => [...text.matchAll(/\d+/g)].map(m => BigInt(m[0]));
for (const [i,[name,g,c,r,f,status,level]] of cases.entries()) {
  const actual = words(host.call(artifact,"inferPi","array-u64",[host.arrayU64(g),host.arrayU64(c),host.i64(r),host.i64(f)]));
  assert.deepEqual(actual, words(native[i]), `WASM/Lean: ${name}`);
  assert.equal(actual[0], BigInt(status), name);
  if (status === 0) {
    const offset = 2 + Number(actual[1]) * 3;
    if (level === "Pi") assert.equal(actual[offset], 2n, name);
    else assert.deepEqual(actual.slice(offset,offset+3), [0n,BigInt(level),0n], name);
  } else assert.deepEqual(actual, [BigInt(status)], name);
}
console.log(`checked ${cases.length} M0.5 WASM/standard-Lean Pi judgments; artifact: ${artifact}`);
