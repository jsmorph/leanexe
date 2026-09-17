#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const assert = require("node:assert/strict");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const directory = path.join(root, "build/tiny-gpt2");
const wasm = path.join(directory, "sequence-inference.wasm");
const bound = 0x4024000000000000n;

function parseArray(text) {
  assert.match(text, /^\[(?:[0-9]+(?:, [0-9]+)*)?\]$/);
  return text === "[]" ? [] : text.slice(1, -1).split(", ").map(BigInt);
}

function main() {
  const args = process.argv.slice(2);
  if (args.length !== 0 && (args.length !== 2 || args[0] !== "--checkpoint")) {
    throw new Error("usage: node test/tiny_gpt2_sequence.js [--checkpoint FILE]");
  }
  const fixturePath = path.join(directory, args.length ? "sequence-trained-fixture.json" : "sequence-fixture.json");
  runChecked([path.join(root, ".venv-tiny-gpt2/bin/python"), "training/tiny-gpt2/sequence_fixture.py",
    "--output", fixturePath, ...args], { cwd: root, encoding: "utf8" });
  runChecked(["lake", "--log-level=error", "build", "Project.TinyGpt2Seq.Inference"],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.TinyGpt2Seq.Inference", "--entry", "Project.TinyGpt2Seq.inferChecked",
    "--out", wasm], { cwd: proofRoot, encoding: "utf8" });
  const fixture = JSON.parse(fs.readFileSync(fixturePath, "utf8"));
  assert.equal(fixture.weights.length, 2984);
  const expected = runChecked(["lake", "env", "lean", "--run", "Project/TinyGpt2Seq/NativeTest.lean", fixturePath],
    { cwd: proofRoot, encoding: "utf8", timeout: 180000 }).stdout.trim().split(/\r?\n/)
    .map(line => line.split(/\s+/).map(BigInt));
  assert.equal(expected.length, fixture.cases.length);
  let maximumDifference = 0;
  for (const [index, c] of fixture.cases.entries()) {
    const result = host.callStats(wasm, "inferChecked", "array-u64",
      [host.arrayU64(fixture.weights), host.i64(bound), host.arrayU64(c.tokens)]);
    const actual = parseArray(result.result);
    assert.equal(actual.length, 256);
    assert.deepEqual(actual, expected[index], `Source differs at context length ${c.tokens.length}`);
    for (const [token, word] of actual.entries()) {
      const bytes = Buffer.alloc(8);
      bytes.writeBigUInt64LE(word);
      const value = bytes.readDoubleLE();
      assert(Number.isFinite(value));
      const difference = Math.abs(value - c.logits[token]);
      maximumDifference = Math.max(maximumDifference, difference);
      assert(difference < 1e-8, `PyTorch differs at case ${index}, token ${token}`);
    }
  }
  const nanWeights = [...fixture.weights];
  nanWeights[0] = "9221120237041090560";
  const rejected = [
    [fixture.weights, bound, []],
    [fixture.weights, bound, Array(129).fill(0)],
    [fixture.weights, bound, [256]],
    [fixture.weights, bound, [...Array(127).fill(0), 256]],
    [fixture.weights.slice(1), bound, [0]],
    [[...fixture.weights, "0"], bound, [0]],
    [nanWeights, bound, [0]],
    [fixture.weights, 0x4026000000000000n, [0]],
  ];
  for (const [weights, b, tokens] of rejected) {
    const output = host.call(wasm, "inferChecked", "array-u64",
      [host.arrayU64(weights), host.i64(b), host.arrayU64(tokens)]);
    assert.deepEqual(parseArray(output), []);
  }
  process.stdout.write(`Checked ${256 * expected.length} sequence logits against the Lean source and ` +
    `${rejected.length} rejection cases; maximum empirical PyTorch difference ${maximumDifference}\n`);
}

try { main(); }
catch (error) { process.stderr.write(`${error.stack}\n`); process.exitCode = 1; }
