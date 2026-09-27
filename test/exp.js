#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { prepare, invoke, invokeArray, runExample } = require("../tools/seminum");
const { runChecked } = require("../tools/run-process");
const { ensureHost } = require("../tools/wasmtime-host");

const root = path.resolve(__dirname, "..");
const directory = path.join(root, "build/seminum");
const options = { cwd: root, encoding: "utf8", timeout: 120000, maxBuffer: 32 * 1024 * 1024 };
function bits(x) {
  const buffer = Buffer.alloc(8);
  buffer.writeDoubleLE(x);
  return buffer.readBigUInt64LE();
}
function value(word) {
  const buffer = Buffer.alloc(8);
  buffer.writeBigUInt64LE(word);
  return buffer.readDoubleLE();
}

function main() {
  prepare();
  const input = path.join(directory, "exp-input.txt");
  const nativeFile = path.join(directory, "exp-native.txt");
  runChecked(["python3", "test/exp-reference.py", "generate", input], options);
  const words = fs.readFileSync(input, "utf8").trim().split("\n").map(BigInt);
  runChecked(["lake", "env", "lean", "--run", "test/ExpNative.lean", input, nativeFile],
    { ...options, timeout: 300000 });
  const native = fs.readFileSync(nativeFile, "utf8").trim().split("\n").map(line => line.split(" ").map(BigInt));
  assert.equal(native.length, words.length);
  const results = [];
  for (let start = 0; start < words.length; start += 1024) {
    const batch = words.slice(start, start + 1024);
    const wasm = invokeArray("expBatch", batch);
    assert.equal(wasm.length, batch.length);
    batch.forEach((word, i) => {
      const [port, leanExp] = native[start + i];
      assert.equal(wasm[i], port, `WASM/native port at ${word.toString(16)}`);
      results.push({ input: word.toString(), wasm: wasm[i].toString(),
        leanExp: leanExp.toString(), javascript: bits(Math.exp(value(word))).toString() });
    });
  }
  const resultFile = path.join(directory, "exp-results.json");
  fs.writeFileSync(resultFile, JSON.stringify(results));
  const report = runChecked(["python3", "test/exp-reference.py", "check", resultFile], options).stdout;
  fs.writeFileSync(path.join(directory, "exp-accuracy.json"), report);
  process.stdout.write(report);

  for (const x of [-1000, -100, -10, -1, -0, 0, 1, 10, 100, 1000]) {
    const y = value(invoke("sigmoid", 1, [`i64:${bits(x)}`])[0]);
    const z = Math.exp(-Math.abs(x));
    const expected = x < 0 ? z / (1 + z) : 1 / (1 + z);
    assert.ok(Math.abs(y - expected) <= 2 * Number.EPSILON * Math.abs(expected), `sigmoid(${x})`);
  }
  assert.equal(runExample("exp", ["1"]), "2.718281828459045");
  assert.equal(runExample("exp-bits", ["fff0000000000000"]), "0000000000000000");
  assert.equal(runExample("exp-bits", ["7ff0000000000001"]), "7ff8000000000000");
  assert.equal(runExample("sigmoid", ["0"]), "0.5");
  for (const x of [0, 1, -1, 512, -512, 710, -745, -1000, Infinity, -Infinity, NaN]) {
    const stats = runChecked([ensureHost(), "call-stats", path.join(directory, "examples.wasm"),
      "exp", "i64", `i64:${bits(x)}`], options).stdout;
    assert.match(stats, /^stats 0 0 0 0$/m);
  }
  process.stdout.write(`Passed ${words.length} WASM/native port comparisons, accuracy target, sigmoid, CLI, and allocation tests\n`);
}

try { main(); }
catch (error) { process.stderr.write(`${error.stack}\n`); process.exitCode = 1; }
