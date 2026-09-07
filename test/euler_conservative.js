#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");
const moduleName = "LeanExe.Examples.EulerConservative";
const entry = "sideCheckedBits";
const compiler = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const run = args => runChecked(args, { encoding: "utf8", timeout: 120000 }).stdout;
const words = text => text.split(" ").map(x => BigInt("0x" + x));
const one = 0x3ff0000000000000n, energy = 0x4004000000000000n;
const sign = 0x8000000000000000n, max = 0x7fefffffffffffffn;
// Fixed host IEEE reference words are regression evidence, not formal claims.
const accepted = [
  ["Sod left", [one, 0n, energy], "0 0 3ff0000000000000 3ff2ee73dadc9b57 0 3ff0000000000000 0"],
  ["Sod right", words("3fc0000000000000 0 3fd0000000000000"), "0 0 3fb999999999999a 3ff0eecc87dbfa54 0 3fb999999999999a 0"],
  ["negative momentum", words("3fe0000000000000 bfd0000000000000 3ff0000000000000"), "0 bfe0000000000000 3fd8000000000000 3ff86526aa25a13a bfd0000000000000 3fe0000000000000 bfe6000000000000"],
  ["upper velocity boundary", [one, one, one], "0 3ff0000000000000 3fc999999999999a 3ff8776643edfd2a 3ff0000000000000 3ff3333333333333 3ff3333333333333"],
  ["lower velocity boundary", [one, one | sign, one], "0 bff0000000000000 3fc999999999999a 3ff8776643edfd2a bff0000000000000 3ff3333333333333 bff3333333333333"],
  ["negative zero momentum", [one, sign, energy], "0 8000000000000000 3ff0000000000000 3ff2ee73dadc9b57 8000000000000000 3ff0000000000000 8000000000000000"],
];
const rejected = [
  ["zero density", [0n, 0n, energy]],
  ["negative zero density", [sign, 0n, energy]],
  ["negative density", [one | sign, 0n, energy]],
  ["zero energy", [one, 0n, 0n]],
  ["negative zero energy", [one, 0n, sign]],
  ["negative energy", [one, 0n, energy | sign]],
  ["energy adjacent below density", [one, 0n, one - 1n]],
  ["momentum adjacent above density", [one, one + 1n, energy]],
  ["negative momentum adjacent outside", [one, (one + 1n) | sign, energy]],
  ["rounded pressure underflow", [1n, 0n, 1n]],
  ["pressure ratio overflow", [1n, 0n, one]],
  ["enthalpy overflow", [one, 0n, max]],
  // Published cancellation example: https://github.com/lanyonai/CompressibleEuler/issues/2
  ["published cancellation", words("3ff3be3969ca97cb 41981433e88dacc6 432d5df2b6bc70d7")],
  // Published one-sided NaN example: https://github.com/lanyonai/CompressibleEuler/issues/3
  ["published one-sided NaN", words("3fe999999999999a 400428f5c28f5c29 400fc083126e978d")],
];
for (const special of words("7ff0000000000000 fff0000000000000 7ff0000000000001 fff0000000000001 7ff8000000000000 fff8000000000000")) {
  for (let slot = 0; slot < 3; slot++) {
    const inputs = [one, 0n, energy]; inputs[slot] = special;
    rejected.push(["nonfinite slot " + slot + " word " + special.toString(16), inputs]);
  }
}
function main() {
  const output = fs.mkdtempSync(path.join("tmp", "euler-conservative-"));
  const wasm = path.join(output, entry + ".wasm"), watPath = path.join(output, entry + ".wat");
  const args = ["--module", moduleName, "--entry", moduleName + "." + entry];
  run([compiler, "compile", ...args, "--out", wasm]);
  run([compiler, "compile-wat", ...args, "--out", watPath]);
  const wat = fs.readFileSync(watPath, "utf8"), ir = run([compiler, "dump-ir", ...args]);
  for (const [op, count] of [["Sub", 1], ["Div", 2], ["Mul", 5], ["Add", 3], ["Sqrt", 1]]) {
    assert.equal(ir.split("f64" + op + "Bits").length - 1, count, "IR " + op);
    assert.equal(wat.split("f64." + op.toLowerCase()).length - 1, count, "WAT " + op);
  }
  for (const [name, inputs, expected] of accepted)
    assert.deepEqual(callI64Slots(wasm, entry, 7, inputs), words(expected), name);
  for (const [name, inputs] of rejected)
    assert.deepEqual(callI64Slots(wasm, entry, 7, inputs), [1n, 0n, 0n, 0n, 0n, 0n, 0n], name);
  console.log("Checked " + accepted.length + " accepted and " + rejected.length + " rejected conservative sides; retained " + output);
}
try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
