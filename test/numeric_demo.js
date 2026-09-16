#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const { runDemo } = require("../tools/numeric-demo");
const { runChecked } = require("../tools/run-process");

const root = path.resolve(__dirname, "..");
const words = [0n, 0x8000000000000000n, 0xbff0000000000000n, 0xbfe0000000000000n,
  0x8000000000000001n, 0x800fffffffffffffn, 0xbff0000000000001n,
  1n, 0x3ff0000000000000n, 0x7ff0000000000000n, 0xfff0000000000000n,
  0x7ff8000000000000n];

function main() {
  const reference = runChecked(["lake", "env", "lean", "--run", "Project/ExpSmall/NativeTest.lean",
    ...words.map(String)], { cwd: path.join(root, "proofs/talos/lean"), encoding: "utf8" })
    .stdout.trim().split(/\r?\n/).map(line => line.split(" ").map(BigInt));
  assert.equal(reference.length, words.length);
  for (const [index, word] of words.entries()) {
    const output = runDemo("exp-small", { x_bits: word.toString(16).padStart(16, "0") });
    assert.equal(BigInt(output.status), reference[index][0]);
    assert.equal(BigInt(`0x${output.bits}`), reference[index][1]);
    assert.equal(output.status, index < 6 ? 0 : 1);
    if (index < 2) assert.equal(output.bits, "3ff0000000000000");
    if (output.status === 0) {
      const bytes = Buffer.alloc(8);
      bytes.writeBigUInt64LE(word);
      assert.ok(output.value > 0);
      assert.ok(Math.abs(output.value - Math.exp(bytes.readDoubleLE())) <= 1 / 4000);
    } else {
      assert.equal(output.bits, "0000000000000000");
      assert.equal(output.absolute_error_bound, undefined);
    }
  }
  for (const bad of [null, [], {}, { x_bits: 0 }, { x_bits: "0" },
    { x_bits: "gggggggggggggggg" }, { x_bits: "0000000000000000", extra: 0 }]) {
    assert.throws(() => runDemo("exp-small", bad));
  }
  console.log("Checked exponential WASM against the native bit model, interval boundaries, signed zeros, subnormals, rejection, and CLI input validation");
}

try { main(); }
catch (error) { console.error(error.stack); process.exitCode = 1; }
