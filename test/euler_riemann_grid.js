"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.EulerRiemann.Grid";
const namespace = "LeanExe.Examples.EulerRiemann";
const compiler = process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm";
const run = args => runChecked(args, {
  encoding: "utf8", timeout: 180000, maxBuffer: 16 * 1024 * 1024,
}).stdout;

function main() {
  run(["lake", "build", moduleName]);
  const output = fs.mkdtempSync(path.join("tmp", "euler-riemann-grid-"));
  const artifacts = new Map();
  for (const entry of ["gridIndices", "neighbor", "lowerFractionNumerator"]) {
    const wasm = path.join(output, entry + ".wasm");
    run([compiler, "compile", "--module", moduleName,
      "--entry", namespace + "." + entry, "--out", wasm]);
    artifacts.set(entry, wasm);
  }
  const call = (entry, kind, args) => run([
    "tools/leanrun", "--timeout", "30s", host.ensureHost(), "call",
    artifacts.get(entry), entry, kind, ...args.map(host.i64),
  ]).trim();
  let checks = 0;
  for (const n of [0, 1, 2, 3, 192, 800, 801]) {
    const values = JSON.parse(call("gridIndices", "array-u64", [n]));
    const count = n >= 2 && n <= 800 ? n * n : 0;
    assert.equal(values.length, count);
    for (let i = 0; i < count; i++) assert.equal(values[i], i);
    checks++;
  }
  for (const index of [0, 1, 2, 3, 4, 5, 6, 7, 8]) {
    const x = index % 3, y = Math.floor(index / 3);
    for (const axisY of [false, true]) for (const forward of [false, true]) {
      const direction = forward ? 1 : -1;
      const nx = axisY ? x : Math.max(0, Math.min(2, x + direction));
      const ny = axisY ? Math.max(0, Math.min(2, y + direction)) : y;
      assert.equal(Number(call("neighbor", "i64", [3, index, +axisY, +forward])), ny * 3 + nx);
      checks++;
    }
  }
  for (const [n, coordinate, expected] of [
    [192, 152, 5], [192, 153, 3], [192, 154, 0],
    [800, 639, 5], [800, 640, 0],
  ]) {
    assert.equal(Number(call("lowerFractionNumerator", "i64", [n, coordinate])), expected);
    checks++;
  }
  console.log(`Passed ${checks} grid geometry and index tests; retained ${output}`);
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
