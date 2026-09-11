"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const proofRoot = path.resolve("proofs/talos/lean");
const compiler = path.resolve(process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm");
const run = args => runChecked(args, {
  encoding: "utf8", timeout: 180000, maxBuffer: 8 * 1024 * 1024,
}).stdout.trim();
const proofEnv = args => run(["lake", "-d", proofRoot, "env", ...args]);
const isNaN = word => (word & 0x7ff0000000000000n) === 0x7ff0000000000000n &&
  (word & 0xfffffffffffffn) !== 0n;

function main() {
  run(["lake", "-d", proofRoot, "build", "Project.IEEE64Source.Source"]);
  run(["lake", "build", "LeanExe.Examples.Float64Bits"]);
  const rows = proofEnv(["lean", "--run", path.resolve("test/ieee64_source.lean")])
    .split(/\r?\n/).map(line => {
      const fields = line.split(" ");
      assert.equal(fields.length, 4, line);
      return [fields[0], ...fields.slice(1).map(BigInt)];
    });
  const output = fs.mkdtempSync(path.join("tmp", "ieee64-source-"));
  const artifacts = new Map();
  for (const entry of new Set(rows.map(row => row[0]))) {
    const wasm = path.resolve(output, entry + ".wasm");
    const legacy = path.resolve(output, entry + "-float.wasm");
    const args = ["--module", "Project.IEEE64Source.Source",
      "--entry", "Project.IEEE64Source." + entry];
    proofEnv([compiler, "compile", ...args, "--out", wasm]);
    run([compiler, "compile", "--module", "LeanExe.Examples.Float64Bits",
      "--entry", "LeanExe.Examples.Float64Bits." + entry, "--out", legacy]);
    assert.deepEqual(fs.readFileSync(wasm), fs.readFileSync(legacy), entry);
    const report = proofEnv([compiler, "report", ...args]);
    assert.ok(report.includes("compiler-recognized UInt64 bit-pattern floating-point intrinsic"));
    artifacts.set(entry, wasm);
  }
  for (const [entry, a, b, expected] of rows) {
    const inputs = entry === "sqrtBits" ? [a] : [a, b];
    const result = BigInt(run(["tools/leanrun", "--timeout", "30s", host.ensureHost(),
      "call", artifacts.get(entry), entry, "i64", ...inputs.map(host.i64)]));
    const word = BigInt.asUintN(64, result);
    if (isNaN(expected)) assert.ok(isNaN(word), entry);
    else assert.equal(word, expected, entry);
  }
  console.log(`Passed ${rows.length} formal IEEE64 source comparisons and six byte-identity checks; retained ${output}`);
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
