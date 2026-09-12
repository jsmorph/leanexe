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
  const proofRoot = path.resolve("proofs/talos/lean");
  const proofEnv = args => run(["lake", "-d", proofRoot, "env", ...args]);
  const traversalModule = "Project.EulerRiemann.TraversalTest";
  run(["lake", "-d", proofRoot, "build", traversalModule]);
  const rows = proofEnv(["lean", "--run", path.resolve("test/euler_riemann_traversal.lean")])
    .trim().split(/\r?\n/).map(line => line.split(" ").map(BigInt));
  const traversalWasm = path.resolve(output, "traversal.wasm");
  proofEnv([path.resolve(compiler), "compile", "--module", traversalModule,
    "--entry", traversalModule + ".sample", "--out", traversalWasm]);
  const arrayWords = (wasm, entry, args) => {
    const text = run(["tools/leanrun", "--timeout", "30s", host.ensureHost(), "call",
      wasm, entry, "array-u64", ...args.map(host.i64)]).trim();
    assert.match(text, /^\[(?:\d+(?:,\s*\d+)*)?\]$/);
    return text.slice(1, -1).split(",").filter(Boolean).map(BigInt);
  };
  for (const [n, advance, ...expected] of rows) {
    const actual = arrayWords(traversalWasm, "sample", [n, advance]);
    assert.deepEqual(actual, expected, `grid ${n}, advance ${advance}`);
    assert.equal(actual.length, 2 + 7 * Number(n * n));
    assert.equal(actual[0], 0n);
    for (let i = 0; i < Number(n * n); i++) {
      assert.equal(actual[2 + 7 * i], BigInt(i));
      assert.equal(actual[2 + 7 * i + 6], 0n);
    }
    checks++;
  }
  const packedWasm = path.resolve(output, "packed.wasm");
  proofEnv([path.resolve(compiler), "compile", "--module", traversalModule,
    "--entry", traversalModule + ".packedInitial", "--out", packedWasm]);
  for (const [n, advance, ...reference] of rows) {
    if (advance !== 0n) continue;
    const count = Number(n * n);
    const density = Array.from({ length: count }, (_, i) => reference[3 + 7 * i]);
    const pressure = Array.from({ length: count }, (_, i) => reference[7 + 7 * i]);
    assert.deepEqual(arrayWords(packedWasm, "packedInitial", [n]),
      [reference[0], 0n, n, n, ...density, ...pressure]);
    checks++;
  }
  console.log(`Passed ${checks} grid geometry, initialization, split-step, and output tests; retained ${output}`);
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
