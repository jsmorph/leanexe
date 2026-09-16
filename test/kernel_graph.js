#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const cases = [
  ["Prop", [0,0,0], 0, 0],
  ["open bvar", [1,0,0], 0, 0],
  ["large bvar is syntax", [1,18446744073709551615n,0], 0, 0],
  ["implication", [0,0,0,1,0,0,2,1,1,2,0,2], 3, 0],
  ["identity", [0,0,0,1,0,0,3,1,1,3,0,2], 3, 0],
  ["sharing", [0,0,0,2,0,0,2,1,1], 2, 0],
  ["empty", [], 0, 4],
  ["truncated", [0,0], 0, 4],
  ["root outside", [0,0,0], 1, 4],
  ["huge root", [0,0,0], 18446744073709551615n, 4],
  ["unknown tag", [9,0,0], 0, 4],
  ["sort spare field", [0,0,1], 0, 4],
  ["bvar spare field", [1,0,1], 0, 4],
  ["self-cycle", [2,0,0], 0, 4],
  ["forward child", [0,0,0,2,0,2,1,0,0], 1, 4],
  ["missing child", [0,0,0,3,7,0], 1, 4],
  ["invalid unreachable node", [0,0,0,9,0,0], 0, 4],
];
const artifact = compile("Graph", "validateGraph", "m0-2");
const native = reference("Graph", cases.map(([,g,r]) => `(validateGraph ${leanArray(g)} ${r}).toNat`));
for (const [i,[name,g,root,expected]] of cases.entries()) {
  assert.equal(BigInt(native[i]), BigInt(expected), `Lean: ${name}`);
  assert.equal(host.callI64(artifact, "validateGraph", [host.arrayU64(g), host.i64(root)]),
    BigInt(expected), `WASM: ${name}`);
}
console.log(`checked ${cases.length} M0.2 WASM/standard-Lean graphs; artifact: ${artifact}`);
