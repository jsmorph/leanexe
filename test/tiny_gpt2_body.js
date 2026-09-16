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
const checkpoint = process.argv.length === 4 && process.argv[2] === "--checkpoint" ? process.argv[3] : null;
const fixturePath = path.join(directory, checkpoint ? "trained-fixture.json" : "initialization.json");
const wasm = path.join(directory, "hidden.wasm");
const headWasm = path.join(directory, "logit.wasm");

function main() {
  if (process.argv.length !== 2 && !checkpoint) throw new Error("usage: tiny_gpt2_body.js [--checkpoint PATH]");
  fs.mkdirSync(directory, { recursive: true });
  runChecked([path.join(root, ".venv-tiny-gpt2/bin/python"), "training/tiny-gpt2/fixture.py",
    "--output", fixturePath, ...(checkpoint ? ["--checkpoint", checkpoint] : [])], { cwd: root, encoding: "utf8" });
  runChecked(["lake", "--log-level=error", "build", "Project.TinyGpt2.Inference"],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.TinyGpt2.Model", "--entry", "Project.TinyGpt2.hidden", "--out", wasm],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.TinyGpt2.Model", "--entry", "Project.TinyGpt2.logit", "--out", headWasm],
    { cwd: proofRoot, encoding: "utf8" });
  const fixture = JSON.parse(fs.readFileSync(fixturePath, "utf8"));
  const native = runChecked(["lake", "env", "lean", "--run", "Project/TinyGpt2/NativeTest.lean", fixturePath],
    { cwd: proofRoot, encoding: "utf8", timeout: 180000 }).stdout.trim().split(/\r?\n/)
    .map(line => line.split(/\s+/).map(BigInt));
  assert.equal(native.length, fixture.cases.length);
  let maximumDifference = 0;
  let maximumLogitDifference = 0;
  const outputs = fixture.cases.map((c, i) => {
    const result = host.callStats(wasm, "hidden", "slots:4",
      [host.arrayU64(fixture.weights), ...c.tokens.map(host.i64), host.i64(c.position)]);
    const actual = result.result.split(/\s+/).map(BigInt);
    assert.equal(native[i].length, 8);
    assert.deepEqual(actual, native[i].slice(0, 4), `native bit model differs at case ${i}`);
    assert.equal(result.allocs, 1n, "hidden-state inference allocated beyond its weight input");
    actual.forEach((word, j) => {
      const bytes = Buffer.alloc(8);
      bytes.writeBigUInt64LE(word);
      const value = bytes.readDoubleLE();
      assert(Number.isFinite(value));
      const difference = Math.abs(value - c.reference[j]);
      maximumDifference = Math.max(maximumDifference, difference);
      assert(difference < 0.01, `PyTorch hidden-state comparison differs at case ${i}, coordinate ${j}`);
    });
    [0, 32, 65, 255].forEach((token, j) => {
      const output = host.callI64(headWasm, "logit",
        [host.arrayU64(fixture.weights), ...actual.map(host.i64), host.i64(token)]);
      assert.equal(output, native[i][4 + j], `native logit differs at case ${i}, token ${token}`);
      const bytes = Buffer.alloc(8);
      bytes.writeBigUInt64LE(output);
      const difference = Math.abs(bytes.readDoubleLE() - c.logits[j]);
      maximumLogitDifference = Math.max(maximumLogitDifference, difference);
      assert(difference < 0.01, `PyTorch logit differs at case ${i}, token ${token}`);
    });
    return actual;
  });
  assert.deepEqual(outputs[0], outputs[4], "position zero depends on future tokens");
  assert.deepEqual(outputs[1], outputs[5], "position one depends on future tokens");
  const allNative = runChecked(["lake", "env", "lean", "--run", "Project/TinyGpt2/NativeTest.lean", fixturePath, "all"],
    { cwd: proofRoot, encoding: "utf8", timeout: 180000 }).stdout.trim().split(/\r?\n/)
    .map(line => line.split(/\s+/).map(BigInt));
  const finalCases = fixture.cases.filter(c => c.position === 3);
  assert.equal(allNative.length, finalCases.length);
  let allDifference = 0;
  for (const [i, c] of finalCases.entries()) {
    const text = host.call(path.join(root, "data/tiny-gpt2-v1/inference.wasm"), "infer", "array-u64",
      [host.arrayU64(fixture.weights), ...c.tokens.map(host.i64)]);
    assert.match(text, /^\[[0-9]+(?:, [0-9]+)*\]$/);
    const actual = text.slice(1, -1).split(", ").map(BigInt);
    assert.equal(actual.length, 256);
    assert.deepEqual(actual, allNative[i], `native full inference differs at case ${i}`);
    actual.forEach((word, token) => {
      const bytes = Buffer.alloc(8);
      bytes.writeBigUInt64LE(word);
      const difference = Math.abs(bytes.readDoubleLE() - c.all_logits[token]);
      allDifference = Math.max(allDifference, difference);
      assert(difference < 0.01, `PyTorch full inference differs at case ${i}, token ${token}`);
    });
  }
  if (checkpoint === "data/tiny-gpt2-v1/checkpoint.json") {
    const cli = JSON.parse(runChecked([path.join(root, "tools/tiny-gpt2.js"), "--text", "To b"],
      { cwd: root, encoding: "utf8" }).stdout);
    assert.deepEqual(cli.tokens, [84, 111, 32, 98]);
    assert.deepEqual(cli.logits_bits.map(x => BigInt(`0x${x}`)), allNative.at(-1));
  }
  process.stdout.write(`Checked ${native.length} ${checkpoint ? "trained" : "initialized"} model rows against the native bit model; ` +
    `maximum empirical PyTorch hidden/logit differences ${maximumDifference}/${maximumLogitDifference}\n` +
    `Checked ${finalCases.length * 256} complete inference logits; maximum empirical PyTorch difference ${allDifference}\n`);
}

try { main(); }
catch (error) { process.stderr.write(`${error.stack}\n`); process.exitCode = 1; }
