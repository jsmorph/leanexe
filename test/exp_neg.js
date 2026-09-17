#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const wasm = path.join(root, "build/exp-neg.wasm");

function word(value) {
  const bytes = Buffer.alloc(8);
  bytes.writeDoubleLE(value);
  return bytes.readBigUInt64LE();
}

function value(bits) {
  const bytes = Buffer.alloc(8);
  bytes.writeBigUInt64LE(bits);
  return bytes.readDoubleLE();
}

const inputs = [0n, word(-0), 0x8000000000000001n, word(-0.25), word(-0.75),
  ...[1, 2, 4, 8, 16, 32, 64].flatMap(x => [word(-x)-1n, word(-x), word(-x)+1n]),
  word(-100), 0xFFEFFFFFFFFFFFFFn, 1n, word(1), word(Infinity), word(-Infinity),
  0x7FF8000000000000n, 0xFFF8000000000000n];

function main() {
  runChecked(["lake", "--log-level=error", "build", "Project.ExpNeg.Polynomial"],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.ExpNeg.Model", "--entry", "Project.ExpNeg.expNeg", "--out", wasm],
    { cwd: proofRoot, encoding: "utf8" });
  const native = runChecked(["lake", "env", "lean", "--run", "Project/ExpNeg/NativeTest.lean",
    ...inputs.map(String)], { cwd: proofRoot, encoding: "utf8", timeout: 120000 }).stdout.trim()
    .split(/\r?\n/).map(line => line.split(/\s+/).map(BigInt));
  assert.equal(native.length, inputs.length);
  let maximumError = 0;
  for (const [i, input] of inputs.entries()) {
    const result = callI64Slots(wasm, "expNeg", 2, [input]);
    assert.deepEqual(result, native[i], `Native bit model differs for ${input}`);
    const x = value(input);
    if (!Number.isFinite(x) || x > 0) {
      assert.deepEqual(result, [1n, 0n]);
    } else if (x < -64) {
      assert.deepEqual(result, [0n, 0n]);
    } else {
      assert.equal(result[0], 0n);
      const y = value(result[1]);
      assert(Number.isFinite(y) && y > 0);
      const error = Math.abs(y-Math.exp(x));
      maximumError = Math.max(maximumError, error);
      assert(error <= 2e-14*Math.exp(x), `Exponential comparison differs at ${x}`);
    }
  }
  process.stdout.write(`Checked ${inputs.length} exponential WASM results against the native bit model; ` +
    `maximum empirical absolute error ${maximumError}\n`);
}

main();
