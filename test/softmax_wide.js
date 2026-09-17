#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const wasm = path.join(root, "build/softmax-wide.wasm");

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

const cases = [];
for (const n of [1, 2, 3, 4]) {
  for (const scores of [[0, 0, 0, 0], [0, -1, -8, -64], [100, 99, 92, 36],
    [-100, -99, -92, -36], [0, -64, -65, -1000000], [1200000, -1200000, 0, 5],
    [1e100, 1e100, -1e100, -1e100], [-0, 0, -Number.MIN_VALUE, Number.MIN_VALUE]]) {
    cases.push([BigInt(n), ...scores.map(word)]);
  }
}
for (const boundary of [word(-64)-1n, word(-64), word(-64)+1n]) {
  cases.push([4n, 0n, boundary, word(-65), word(-1)]);
}

function main() {
  runChecked(["lake", "--log-level=error", "build", "Project.SoftmaxWide.Model"],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.SoftmaxWide.Model", "--entry", "Project.SoftmaxWide.compute", "--out", wasm],
    { cwd: proofRoot, encoding: "utf8" });
  const native = runChecked(["lake", "env", "lean", "--run", "Project/SoftmaxWide/NativeTest.lean",
    ...cases.flat().map(String)], { cwd: proofRoot, encoding: "utf8", timeout: 120000 }).stdout.trim()
    .split(/\r?\n/).map(line => line.split(/\s+/).map(BigInt));
  assert.equal(native.length, cases.length);
  let maximumError = 0;
  for (const [i, inputs] of cases.entries()) {
    const result = callI64Slots(wasm, "compute", 5, inputs);
    assert.deepEqual(result, native[i], `Native bit model differs in case ${i}`);
    assert.equal(result[0], 0n);
    const n = Number(inputs[0]);
    const scores = inputs.slice(1).map(value);
    const maximum = Math.max(...scores.slice(0, n));
    const weights = scores.map((x, j) => j < n ? Math.exp(x-maximum) : 0);
    const total = weights.reduce((a, b) => a+b, 0);
    const actual = result.slice(1).map(value);
    assert(actual.every(x => Number.isFinite(x) && x >= 0));
    assert(Math.abs(actual.reduce((a, b) => a+b, 0)-1) <= 1e-15);
    for (let j = 0; j < 4; j++) {
      if (j >= n) assert.equal(result[j+1], 0n);
      const expected = weights[j]/total;
      const error = Math.abs(actual[j]-expected);
      maximumError = Math.max(maximumError, error);
      assert(error <= 2e-14*expected+1e-27, `Softmax comparison differs in case ${i}, output ${j}`);
    }
  }
  process.stdout.write(`Checked ${cases.length} softmax WASM rows against the native bit model; ` +
    `maximum empirical absolute error ${maximumError}\n`);
}

main();
