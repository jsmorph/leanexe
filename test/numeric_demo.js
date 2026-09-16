#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const { runDemo } = require("../tools/numeric-demo");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");

const root = path.resolve(__dirname, "..");
const words = [0n, 0x8000000000000000n, 0xbff0000000000000n, 0xbfe0000000000000n,
  0x8000000000000001n, 0x800fffffffffffffn, 0xbff0000000000001n,
  1n, 0x3ff0000000000000n, 0x7ff0000000000000n, 0xfff0000000000000n,
  0x7ff8000000000000n];

function bits(value) {
  const bytes = Buffer.alloc(8);
  bytes.writeDoubleLE(value);
  return bytes.readBigUInt64LE();
}

function decoded(word) {
  const bytes = Buffer.alloc(8);
  bytes.writeBigUInt64LE(word);
  return bytes.readDoubleLE();
}

function checkSoftmax() {
  const rows = [[0], [-0], [4], [-4], [0, 0], [0, -0, 0, -0],
    [-4, 4], [4, -4], [-1, -2], [-2, -1], [0, -1], [-1, 0],
    [0, 1, 2], [2, 1, 0], [-4, -3, -2, -1], [4, 3, 2, 1],
    [1, 4, 2, 3], [1, 2, 4, 3], [1, 2, 3, 4], [4, 4, 4],
    [5, 0], [Infinity], [-Infinity], [NaN]].map(row => row.map(bits));
  rows.push([1n, 0x8000000000000001n], [0x400fffffffffffffn, bits(-4)],
    [0x4010000000000001n], [0xc010000000000001n]);
  const arguments_ = rows.map(row => [BigInt(row.length), ...row, ...Array(4-row.length).fill(0n)]);
  const invalidCounts = [[0n, 0n, 0n, 0n, 0n], [5n, 0n, 0n, 0n, 0n],
    [0xffffffffffffffffn, 0n, 0n, 0n, 0n]];
  const reference = runChecked(["lake", "env", "lean", "--run", "Project/Softmax/NativeTest.lean",
    ...[...arguments_, ...invalidCounts].flat().map(String)],
    { cwd: path.join(root, "proofs/talos/lean"), encoding: "utf8" })
    .stdout.trim().split(/\r?\n/).map(line => line.split(" ").map(BigInt));
  assert.equal(reference.length, rows.length + invalidCounts.length);
  for (const [index, row] of rows.entries()) {
    const output = runDemo("softmax", { scores_bits: row.map(word => word.toString(16).padStart(16, "0")) });
    assert.deepEqual([BigInt(output.status), ...output.probabilities_bits.map(word => BigInt(`0x${word}`))], reference[index]);
    const values = row.map(decoded);
    const accepted = values.every(value => Number.isFinite(value) && Math.abs(value) <= 4);
    assert.equal(output.status, accepted ? 0 : 1);
    if (accepted) {
      const maximum = Math.max(...values);
      const exactWeights = values.map(value => Math.exp(value-maximum));
      const total = exactWeights.reduce((sum, value) => sum+value, 0);
      for (let i = 0; i < 4; ++i) {
        if (i < row.length) {
          assert.ok(output.probabilities[i] > 0);
          assert.ok(Math.abs(output.probabilities[i] - exactWeights[i]/total) <= 1/64);
        } else {
          assert.equal(output.probabilities_bits[i], "0000000000000000");
        }
      }
      assert.ok(Math.abs(output.probabilities.reduce((sum, value) => sum+value, 0)-1) <= 2**-47);
    } else {
      assert.deepEqual(output.probabilities_bits, Array(4).fill("0000000000000000"));
      assert.equal(output.absolute_error_bound, undefined);
    }
  }
  for (const [index, row] of invalidCounts.entries()) {
    const actual = callI64Slots(path.join(root, "proofs/talos/.generated/softmax/program.wasm"), "softmax", 5, row);
    assert.deepEqual(actual, reference[rows.length+index]);
    assert.deepEqual(actual, [1n, 0n, 0n, 0n, 0n]);
  }
  for (const input of [{}, {scores_bits: []}, {scores_bits: Array(5).fill("0000000000000000")},
    {scores_bits: [0]}, {scores_bits: ["0"]}, {scores_bits: ["0000000000000000"], extra: 0}]) {
    assert.throws(() => runDemo("softmax", input));
  }
  const decimalOutput = JSON.parse(runChecked([process.execPath, path.join(root, "tools/numeric-demo.js"),
    "softmax", "--scores", "0", "1", "2"], {encoding: "utf8"}).stdout);
  assert.deepEqual(decimalOutput, runDemo("softmax", {
    scores_bits: [0, 1, 2].map(value => bits(value).toString(16).padStart(16, "0")),
  }));
}

function checkExponential(name, project, words, accepted, bound) {
  const reference = runChecked(["lake", "env", "lean", "--run", `Project/${project}/NativeTest.lean`,
    ...words.map(String)], { cwd: path.join(root, "proofs/talos/lean"), encoding: "utf8" })
    .stdout.trim().split(/\r?\n/).map(line => line.split(" ").map(BigInt));
  assert.equal(reference.length, words.length);
  for (const [index, word] of words.entries()) {
    const output = runDemo(name, { x_bits: word.toString(16).padStart(16, "0") });
    assert.equal(BigInt(output.status), reference[index][0]);
    assert.equal(BigInt(`0x${output.bits}`), reference[index][1]);
    assert.equal(output.status, index < accepted ? 0 : 1);
    if (index < 2) assert.equal(output.bits, "3ff0000000000000");
    if (output.status === 0) {
      const bytes = Buffer.alloc(8);
      bytes.writeBigUInt64LE(word);
      assert.ok(output.value > 0);
      assert.ok(Math.abs(output.value - Math.exp(bytes.readDoubleLE())) <= bound);
    } else {
      assert.equal(output.bits, "0000000000000000");
      assert.equal(output.absolute_error_bound, undefined);
    }
  }
}

function main() {
  checkExponential("exp-small", "ExpSmall", words, 6, 1/4000);
  checkExponential("exp-wide", "ExpWide", [0n, 0x8000000000000000n,
    0xc020000000000000n, 0xc01fffffffffffffn, 0xc010000000000000n,
    0xbff0000000000000n, 0x8000000000000001n, 0x800fffffffffffffn,
    0xc020000000000001n, 1n, 0x3ff0000000000000n, 0x7ff0000000000000n,
    0xfff0000000000000n, 0x7ff8000000000000n], 8, 1/400);
  for (const bad of [null, [], {}, { x_bits: 0 }, { x_bits: "0" },
    { x_bits: "gggggggggggggggg" }, { x_bits: "0000000000000000", extra: 0 }]) {
    assert.throws(() => runDemo("exp-small", bad));
  }
  checkSoftmax();
  console.log("Checked 26 exponential and 31 softmax vectors against the native bit model, including masks, interval boundaries, signed zeros, subnormals, rejection, and CLI input validation");
}

try { main(); }
catch (error) { console.error(error.stack); process.exitCode = 1; }
