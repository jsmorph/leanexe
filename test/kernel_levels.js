#!/usr/bin/env node
const crypto = require("node:crypto");
const { assert, fs, host, compile, leanArray, reference, dir } = require("./kernel_helpers");

const maxWord = 18446744073709551615n;
const cases = [
  ["zero", [0, 0, 0], 0, 0, 0],
  ["successor", [0, 0, 0, 1, 0, 0], 0, 1, 0],
  ["parameter", [2, 0, 0], 1, 0, 0],
  ["last parameter", [2, 2, 0], 3, 0, 0],
  ["high parameter", [2, maxWord - 1n, 0], maxWord, 0, 0],
  ["symbolic successor", [2, 0, 0, 1, 0, 0], 1, 1, 0],
  ["max", [2, 0, 0, 2, 1, 0, 3, 0, 1], 2, 2, 0],
  ["imax", [2, 0, 0, 2, 1, 0, 4, 0, 1], 2, 2, 0],
  ["imax with zero right", [2, 0, 0, 0, 0, 0, 4, 0, 1], 1, 2, 0],
  ["shared children", [0, 0, 0, 3, 0, 0, 4, 1, 1], 0, 2, 0],
  ["nested symbolic levels", [2, 0, 0, 1, 0, 0, 3, 0, 1, 4, 2, 0], 1, 3, 0],
  ["earlier root", [0, 0, 0, 2, 0, 0], 1, 0, 0],
  ["empty", [], 0, 0, 4],
  ["truncated", [0, 0], 0, 0, 4],
  ["trailing word", [0, 0, 0, 1], 0, 0, 4],
  ["root outside", [0, 0, 0], 0, 1, 4],
  ["huge root", [0, 0, 0], 0, maxWord, 4],
  ["unknown tag", [5, 0, 0], 0, 0, 4],
  ["huge tag", [maxWord, 0, 0], 0, 0, 4],
  ["zero first payload", [0, 1, 0], 0, 0, 4],
  ["zero second payload", [0, 0, 1], 0, 0, 4],
  ["successor spare field", [0, 0, 0, 1, 0, 1], 0, 1, 4],
  ["parameter spare field", [2, 0, 1], 1, 0, 4],
  ["undeclared parameter", [2, 0, 0], 0, 0, 4],
  ["parameter at bound", [2, 3, 0], 3, 0, 4],
  ["parameter at word bound", [2, maxWord, 0], maxWord, 0, 4],
  ["successor self-reference", [1, 0, 0], 0, 0, 4],
  ["successor forward reference", [1, 1, 0, 0, 0, 0], 0, 0, 4],
  ["successor huge reference", [0, 0, 0, 1, maxWord, 0], 0, 1, 4],
  ["max left self-reference", [0, 0, 0, 3, 1, 0], 0, 1, 4],
  ["max right self-reference", [0, 0, 0, 3, 0, 1], 0, 1, 4],
  ["imax left forward reference", [0, 0, 0, 4, 2, 0, 0, 0, 0], 0, 1, 4],
  ["imax right missing reference", [0, 0, 0, 4, 0, maxWord], 0, 1, 4],
  ["invalid unreachable record", [0, 0, 0, 5, 0, 0], 0, 0, 4],
  ["unreachable undeclared parameter", [0, 0, 0, 2, 1, 0], 1, 0, 4],
];

const artifact = compile("Levels", "validateLevels", "m1-2");
const native = reference("Levels", cases.map(([, levels, parameters, root]) =>
  `(validateLevels ${leanArray(levels)} ${parameters} ${root}).toNat`));
for (const [i, [name, levels, parameters, root, expected]] of cases.entries()) {
  assert.equal(BigInt(native[i]), BigInt(expected), `Lean: ${name}`);
  assert.equal(host.callI64(artifact, "validateLevels", [
    host.arrayU64(levels), host.i64(parameters), host.i64(root),
  ]), BigInt(expected), `WASM: ${name}`);
}

const bytes = fs.readFileSync(artifact);
const receipt = {
  artifact,
  bytes: bytes.length,
  sha256: crypto.createHash("sha256").update(bytes).digest("hex"),
  cases: cases.length,
  valid: 0,
  malformed: 4,
};
fs.writeFileSync(`${dir}/m1-2-receipt.json`, JSON.stringify(receipt, null, 2) + "\n");
console.log(`checked ${cases.length} M1.2 symbolic-level tables in WASM and standard Lean; artifact: ${artifact}`);
