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
const fixturePath = path.join(directory, "initialization.json");
const wasm = path.join(directory, "hidden.wasm");
const headWasm = path.join(directory, "logit.wasm");

function main() {
  fs.mkdirSync(directory, { recursive: true });
  runChecked([path.join(root, ".venv-tiny-gpt2/bin/python"), "training/tiny-gpt2/fixture.py",
    "--output", fixturePath], { cwd: root, encoding: "utf8" });
  runChecked(["lake", "--log-level=error", "build", "Project.TinyGpt2.Model"],
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
      assert(difference < 0.01, `PyTorch initialization comparison differs at case ${i}, coordinate ${j}`);
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
  process.stdout.write(`Checked ${native.length} initialized model rows against the native bit model; ` +
    `maximum empirical PyTorch hidden/logit differences ${maximumDifference}/${maximumLogitDifference}\n`);
}

try { main(); }
catch (error) { process.stderr.write(`${error.stack}\n`); process.exitCode = 1; }
