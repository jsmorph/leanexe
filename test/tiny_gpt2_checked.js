#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const wasm = path.join(root, "build/tiny-gpt2/checked-inference.wasm");
const baseline = path.join(root, "data/tiny-gpt2-v1/inference.wasm");
const names = ["token", "position", "query", "key", "value", "attention", "attention_bias",
  "expand", "expand_bias", "contract", "contract_bias", "head", "head_bias",
  "norm1_scale", "norm1_bias", "norm2_scale", "norm2_bias", "norm_final_scale", "norm_final_bias"];
const sign = 0x8000000000000000n;
const magnitude = sign - 1n;

function word(value) {
  const bytes = Buffer.alloc(8);
  bytes.writeDoubleLE(value);
  return bytes.readBigUInt64LE();
}

function main() {
  fs.mkdirSync(path.dirname(wasm), { recursive: true });
  runChecked(["lake", "--log-level=error", "build", "Project.TinyGpt2.Checked"],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.TinyGpt2.Checked", "--entry", "Project.TinyGpt2.inferChecked", "--out", wasm],
    { cwd: proofRoot, encoding: "utf8" });
  const checkpoint = JSON.parse(fs.readFileSync(path.join(root, "data/tiny-gpt2-v1/checkpoint.json")));
  const weights = names.flatMap(name => checkpoint.weights[name].bits.map(bits => BigInt(`0x${bits}`)));
  const tokens = [84n, 111n, 32n, 98n];
  const call = (input, bound, context = tokens) => host.call(wasm, "inferChecked", "array-u64",
    [host.arrayU64(input), host.i64(bound), ...context.map(host.i64)]);
  const cli = (...args) => JSON.parse(runChecked([path.join(root, "tools/tiny-gpt2.js"), ...args],
    { cwd: root, encoding: "utf8" }).stdout);
  const expectedLogits = new Map();

  for (const cap of [10, 1, 0]) {
    const bound = word(cap);
    const clipped = weights.map(value => (value & magnitude) <= bound ? value : (value & sign) | bound);
    const expected = host.call(baseline, "infer", "array-u64",
      [host.arrayU64(clipped), ...tokens.map(host.i64)]);
    assert.equal(call(weights, bound), expected, `Clipped inference at B=${cap}`);
    expectedLogits.set(cap, expected.slice(1, -1).split(", ").map(word =>
      BigInt(word).toString(16).padStart(16, "0")));
  }
  const nonfinite = weights.slice();
  nonfinite[100] = 0x7FF0000000000001n;
  assert.equal(call(nonfinite, word(10)), "[]", "Nonfinite weight rejection");
  assert.equal(call(weights.slice(1), word(10)), "[]", "Short checkpoint rejection");
  assert.equal(call([...weights, 0n], word(10)), "[]", "Long checkpoint rejection");
  assert.equal(call(weights, word(10) + 1n), "[]", "Invalid bound rejection");
  for (let position = 0; position < 4; position++) {
    const invalid = tokens.slice();
    invalid[position] = 256n;
    assert.equal(call(weights, word(10), invalid), "[]", `Token ${position} rejection`);
  }
  const defaultResult = cli("--text", "To b");
  assert.equal(defaultResult.accepted, true);
  assert.deepEqual(defaultResult.logits_bits, expectedLogits.get(10));
  const customResult = cli("--checkpoint", "data/tiny-gpt2-v1/checkpoint.json", "--bound", "1",
    "--tokens", "84", "111", "32", "98");
  assert.equal(customResult.accepted, true);
  assert.deepEqual(customResult.logits_bits, expectedLogits.get(1));
  const zeroResult = cli("--bound", "-0", "--text", "To b");
  assert.equal(zeroResult.accepted, true);
  assert.equal(zeroResult.bound_bits, "8000000000000000");
  assert.deepEqual(zeroResult.logits_bits, expectedLogits.get(0));
  const invalidBound = cli("--text", "To b", "--bound", "11");
  assert.equal(invalidBound.accepted, false);
  assert.deepEqual(invalidBound.logits, []);
  checkpoint.weights.token.bits[0] = "7ff8000000000000";
  const invalidPath = path.join(root, "build/tiny-gpt2/nonfinite-checkpoint.json");
  fs.writeFileSync(invalidPath, JSON.stringify(checkpoint));
  const invalidCheckpoint = cli("--checkpoint", invalidPath, "--text", "To b");
  assert.equal(invalidCheckpoint.accepted, false);
  assert.deepEqual(invalidCheckpoint.logits, []);
  assert.notEqual(invalidCheckpoint.checkpoint_sha256, defaultResult.checkpoint_sha256);
  process.stdout.write("Checked 768 clipped WASM logits, eight rejection cases, and five CLI cases\n");
}

main();
