#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const fs = require("node:fs");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const wasm = path.join(root, "build/tiny-gpt2/prepare-weights.wasm");

function word(value) {
  const bytes = Buffer.alloc(8);
  bytes.writeDoubleLE(value);
  return bytes.readBigUInt64LE();
}

const cases = [
  { bound: word(10), input: [-20, -10, -1, -0, 0, 1, 10, 20].map(word),
    expected: [-10, -10, -1, -0, 0, 1, 10, 10].map(word) },
  { bound: word(0), input: [-2, -0, 0, 2].map(word), expected: [-0, -0, 0, 0].map(word) },
  { bound: word(-0), input: [-2, -0, 0, 2].map(word), expected: [-0, -0, 0, 0].map(word) },
  { bound: word(10), input: [1n, 0x8000000000000001n, 0x7FEFFFFFFFFFFFFFn, 0xFFEFFFFFFFFFFFFFn],
    expected: [1n, 0x8000000000000001n, word(10), word(-10)] },
  { bound: 1n, input: [1n, 2n, 0x8000000000000002n], expected: [1n, 1n, 0x8000000000000001n] },
  { bound: word(10), input: [word(1)], count: 2, expected: [] },
  ...[word(-1), word(10)+1n, word(Infinity), 0x7FF8000000000000n].map(bound =>
    ({ bound, input: [word(1)], expected: [] })),
  ...[word(Infinity), word(-Infinity), 0x7FF0000000000001n, 0xFFF8000000000000n].map(invalid =>
    ({ bound: word(10), input: [word(1), invalid, word(2)], expected: [] })),
];

function main() {
  fs.mkdirSync(path.dirname(wasm), { recursive: true });
  runChecked(["lake", "--log-level=error", "build", "Project.F64Clip.Array"],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.F64Clip.Model", "--entry", "Project.F64Clip.prepare", "--out", wasm],
    { cwd: proofRoot, encoding: "utf8" });
  for (const [i, test] of cases.entries()) {
    const output = host.call(wasm, "prepare", "array-u64",
      [host.i64(test.count ?? test.input.length), host.i64(test.bound), host.arrayU64(test.input)]);
    assert.match(output, /^\[(?:\d+(?:, \d+)*)?\]$/);
    const actual = output === "[]" ? [] : output.slice(1, -1).split(", ").map(BigInt);
    assert.deepEqual(actual, test.expected, `Clipping case ${i}`);
  }
  process.stdout.write(`Checked ${cases.length} WASM clipping and rejection cases\n`);
}

main();
