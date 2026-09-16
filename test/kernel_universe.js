#!/usr/bin/env node
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const run = (args, timeout = 60000) => runChecked(args, { encoding: "utf8", timeout }).stdout.trim();
const dir = ".lake/build/kernel-check";
const artifact = `${dir}/checker-m0-1.wasm`;
const compiler = process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm";
const wasmtime = process.env.WASMTIME || "build/tools/wasmtime/current/wasmtime";
const max = (1n << 64n) - 1n;

run([process.execPath, "tools/check-node-version.js"]);
run(["lake", "build", "LeanExe.KernelCheck.UniverseTest", "lean-wasm"], 900000);
fs.mkdirSync(dir, { recursive: true });
run([compiler, "compile", "--module", "LeanExe.KernelCheck.Universe", "--entry",
  "LeanExe.KernelCheck.checkLevelOp", "--out", artifact], 90000);
const cases = [];
for (const u of [0n, 1n, 2n, 42n, 1n << 63n, max]) {
  for (const v of [0n, 1n, 3n, max]) {
    for (const op of [0n, 1n]) {
      const expected = op === 1n && v === 0n ? 0n : u > v ? u : v;
      cases.push({ args: [op, u, v, expected], result: 0n });
      cases.push({ args: [op, u, v, expected === max ? 0n : expected + 1n], result: 1n });
    }
  }
}
cases.push({ args: [2n, 0n, 0n, 0n], result: 3n });
cases.push({ args: [max, max, max, max], result: 3n });
const reference = path.join(dir, "UniverseReference.lean");
fs.writeFileSync(reference, "import LeanExe.KernelCheck.Universe\n" + cases.map(c =>
  `#eval (LeanExe.KernelCheck.checkLevelOp ${c.args.join(" ")}).toNat`).join("\n") + "\n");
const native = run(["lake", "env", "lean", reference]).split(/\r?\n/);
assert.equal(native.length, cases.length);
for (const [i, c] of cases.entries()) {
  assert.equal(BigInt(native[i]), c.result, `Lean ${c.args}`);
  const output = run([wasmtime, "run", "--invoke", "checkLevelOp", artifact,
    ...c.args.map(v => BigInt.asIntN(64, v).toString())], 15000);
  assert.equal(BigInt(output), c.result, `WASM ${c.args}`);
}
console.log(`checked ${cases.length} M0.1 WASM/standard-Lean universe claims; artifact: ${artifact}`);
