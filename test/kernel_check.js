#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const identity = [0,0,0,1,0,0,1,1,0,2,1,2,2,0,3,3,1,1,3,0,5];
const typeIdentity = [...identity]; typeIdentity[1] = 1;
// ∀ p q : Prop, p → q, falsely proved by λ p q hp => hp.
const falseImplication = [0,0,0,1,0,0,1,1,0,2,2,2,2,0,3,2,0,4,3,2,1,3,0,6,3,0,7];
const wrongBody = [...identity]; wrongBody[17] = 2; // λ p hp => p
const duplicateTypes = [...identity,0,0,0,1,0,0,1,1,0,2,8,9,2,7,10];
const cases = [
  ["closed implication identity",identity,6,4,200,0],
  ["concrete Type identity",typeIdentity,6,4,200,0],
  ["structural equality across distinct IDs",duplicateTypes,6,11,200,0],
  ["false p implies q",falseImplication,8,5,200,1],
  ["wrong body",wrongBody,6,4,200,1],
  ["unused invalid binder",[...identity,3,1,2,3,1,7,3,0,8],9,4,200,1],
  ["wrong type",identity,6,0,200,1],
  ["claimed type is lambda",identity,6,6,200,1],
  ["free proof",identity,1,0,200,1],
  ["exhaustion",identity,6,4,1,5],
  ["invalid claimed root",identity,6,100,200,4],
  ["malformed",[3,0,0],0,0,200,4],
];
const artifact = compile("Check", "checkProof", "m0-6");
const native = reference("Check", cases.map(([,g,r,t,f]) => `(checkProof ${leanArray(g)} ${r} ${t} ${f}).toNat`));
for (const [i,[name,g,r,t,f,expected]] of cases.entries()) {
  assert.equal(BigInt(native[i]), BigInt(expected), `Lean: ${name}`);
  assert.equal(host.callI64(artifact,"checkProof",[host.arrayU64(g),...[r,t,f].map(host.i64)]),BigInt(expected),`WASM: ${name}`);
}
console.log(`checked ${cases.length} M0.6 WASM/standard-Lean closed proof judgments; artifact: ${artifact}`);
