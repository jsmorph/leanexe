#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");

const root = path.resolve(__dirname, "..");
const proof = path.join(root, "proofs/talos/lean");
const wasmtime = process.env.WASMTIME || path.join(root, "build/tools/wasmtime/current/wasmtime");
const wasmTools = process.env.WASM_TOOLS ||
  [...(process.env.PATH || "").split(path.delimiter), path.join(os.homedir(), ".cargo/bin")]
    .map(dir => path.join(dir, "wasm-tools")).find(file => fs.existsSync(file)) || "wasm-tools";
const run = (args, options = {}) => runChecked(args,
  { cwd: root, encoding: "utf8", timeout: 60000, maxBuffer: 16 * 1024 * 1024, ...options }).stdout.trim();

function main() {
  run([wasmtime, "--version"]);
  run(["tools/check-wasm-tools-version.sh"], { env: { ...process.env, WASM_TOOLS: wasmTools } });
  run(["lake", "-d", proof, "build", "Project.Encoding.Tests"], { timeout: 15 * 60000 });
  const audit = run(["lake", "-d", proof, "env", "lean", "Project/Encoding/Audit.lean"],
    { cwd: proof, timeout: 120000 });
  const names = ["unsigned_correct", "signed_correct", "encode_correct", "encode_complete",
    "encode_valid_complete", "encode_behavior"];
  for (const name of names) {
    const report = audit.match(new RegExp(
      `'Wasm\\.Encoding\\.${name}' (does not depend on any axioms|depends on axioms:\\s*\\[([^\\]]*)\\])`));
    assert.ok(report, `missing axiom report for ${name}`);
    const axioms = (report[2] || "").split(",").map(s => s.trim()).filter(Boolean);
    for (const axiom of axioms)
      assert.ok(["propext", "Classical.choice", "Quot.sound"].includes(axiom), `${name}: ${axiom}`);
  }
  fs.mkdirSync(path.join(root, "tmp"), { recursive: true });
  const output = fs.mkdtempSync(path.join(root, "tmp/encoding-"));
  run(["lake", "-d", proof, "env", "lean", "--run", "Project/Encoding/Tests.lean", output],
    { cwd: proof, timeout: 120000 });
  const file = name => path.join(output, `${name}.wasm`);
  for (const name of ["gcd", "float", "validate", "boundaries", "multiple", "wasi", "numeric"])
    run([wasmTools, "validate", file(name)]);
  let count = 0;
  const invoke = (module, entry, inputs, expected) => {
    const result = run([wasmtime, "run", "--invoke", entry, file(module), ...inputs.map(String)]);
    assert.equal(result, expected.map(String).join("\n"), `${module}.${entry}(${inputs})`);
    count++;
  };
  for (const [a, b, expected] of [[0, 0, 0], [54, 24, 6], [1071, 462, 21], [17, 13, 1]])
    invoke("gcd", "gcd", [a, b], [expected]);
  invoke("validate", "validateGeneric", [0, 0], [1]);
  invoke("float", "mulBits", [4607182418800017408n, 4611686018427387904n], [4611686018427387904n]);
  for (const [entry, inputs, expected] of [
    ["min32", [], -2147483648n], ["minus1", [], -1n], ["min64", [], -9223372036854775808n],
    ["max64", [], 9223372036854775807n], ["λ雪", [], 42n],
    ["nested", [0], -65n], ["nested", [5], 5n], ["memory64", [], -9223372036854775808n],
    ["memory8", [], 255n], ["globals", [], 10n], ["global32", [], -1n], ["memoryGrow", [], 2n],
    ["promote", [], 4607182418800017408n], ["demote", [], 1065353216n],
    ["saturate", [], 2147483647n]]) invoke("boundaries", entry, inputs, [expected]);
  invoke("multiple", "pair", [], [-1n, -2147483648n]);
  run([wasmtime, "run", file("wasi")]);
  count++;
  for (const [kind, expected] of [
    ["i32", [0, 0, 1, 0, 1, 11, 0]],
    ["i64", [0, 1, 0, 0, 1, 11, 7, 18, 4, 1, 0, 11, 11, 36, 2]],
    ["f32", [0x40400000, -1082130432, 0x40000000, 0x3f000000]],
    ["f64", [4613937818241073152n, -4616189618054758400n, 4611686018427387904n, 4602678819172646912n]]])
    expected.forEach((value, n) => invoke("numeric", `${kind}_${n}`, [], [value]));
  for (const entry of ["unary32", "unary64", "local", "memory32"])
    invoke("numeric", entry, [], []);
  process.stdout.write(`Checked six theorem axiom sets, seven modules, and ${count} Wasmtime executions\n`);
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
