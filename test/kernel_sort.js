#!/usr/bin/env node

// M0.0: compile the source and check the returned WASM status word against
// mathematical (non-wrapping) universe succession, including UInt64 edges.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");

const compiler = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const outDir = path.join(".lake", "build", "kernel-check");
const artifact = path.join(outDir, "checker-m0-0.wasm");
const max = (1n << 64n) - 1n;

function run(args, timeout) {
  return runChecked(args, { encoding: "utf8", timeout }).stdout.trim();
}

function main() {
  if (process.argv.length !== 2) throw new Error("usage: node test/kernel_sort.js");
  run([process.execPath, "tools/check-node-version.js"], 10000);
  run(["lake", "build", "LeanExe.KernelCheck.SortTest", "lean-wasm"], 900000);
  fs.mkdirSync(outDir, { recursive: true });
  run([compiler, "compile", "--module", "LeanExe.KernelCheck.Sort",
    "--entry", "LeanExe.KernelCheck.checkSort", "--out", artifact], 90000);

  const levels = [0n, 1n, 2n, 42n, (1n << 32n) - 1n,
    (1n << 63n) - 1n, 1n << 63n, max - 1n, max];
  const cases = [];
  for (const level of levels) {
    const claims = new Set([0n, level, max]);
    if (level < max) claims.add(level + 1n);
    for (const claimed of claims) {
      cases.push([level, claimed]);
    }
  }

  // The source-example gate also requires standard-Lean comparison. Evaluate
  // exactly the same corpus, serially, through the existing guarded runner.
  const reference = path.join(outDir, "SortReference.lean");
  const evaluations = cases.map(([level, claimed]) =>
    `#eval (LeanExe.KernelCheck.checkSort ${level} ${claimed}).toNat`);
  fs.writeFileSync(reference, `import LeanExe.KernelCheck.Sort\n${evaluations.join("\n")}\n`);
  const nativeLines = run(["lake", "env", "lean", reference], 60000).split(/\r?\n/);
  assert.equal(nativeLines.length, cases.length, "standard-Lean result count");
  assert(nativeLines.every(line => /^[012]$/.test(line)), "standard-Lean result format");

  for (const [index, [level, claimed]] of cases.entries()) {
    const expected = level === max ? 2n : claimed === level + 1n ? 0n : 1n;
    const label = `checkSort(${level}, ${claimed})`;
    assert.equal(BigInt(nativeLines[index]), expected, `standard Lean: ${label}`);
    // Wasmtime's CLI parses i64 arguments as signed; preserve UInt64 bits.
    const args = [level, claimed].map(value => BigInt.asIntN(64, value).toString());
    const output = run([wasmtime, "run", "--invoke", "checkSort", artifact, ...args], 15000);
    assert.equal(BigInt(output), expected, `WASM: ${label}`);
  }
  process.stdout.write(`checked ${cases.length} M0.0 WASM/standard-Lean sort judgments; artifact: ${artifact}\n`);
}

main();
