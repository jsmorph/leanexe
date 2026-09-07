#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");
const moduleName = "LeanExe.Examples.EulerDynamicFlux";
const compiler = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const run = args => runChecked(args, { encoding: "utf8", timeout: 120000 }).stdout;
const words = text => text.split(" ").map(x => BigInt("0x" + x));
const one = 0x3ff0000000000000n, two = 0x4000000000000000n;
const sign = 0x8000000000000000n, max = 0x7fefffffffffffffn;
const left = words("3ff0000000000000 0 4004000000000000");
const right = words("3fc0000000000000 0 3fd0000000000000");
const special = words("7ff0000000000000 fff0000000000000 7ff0000000000001 fff0000000000001 7ff8000000000000 fff8000000000000");
// Fixed, independently evaluated host IEEE words; regression evidence only.
const acceptedFlux = [
  ["Sod", [...left, ...right], "0 3fe090a55f8107ec 3fe199999999999a 3ff54c4256382ec2 3ff2ee73dadc9b57"],
  ["reversed Sod", [...right, ...left], "0 bfe090a55f8107ec 3fe199999999999a bff54c4256382ec2 3ff2ee73dadc9b57"],
  ["equal state", [...left, ...left], "0 0 3ff0000000000000 0 3ff2ee73dadc9b57"],
  ["opposed velocity", [one, one, one, one, one | sign, one], "0 0 4005d54cbb90982e 0 3ff8776643edfd2a"],
  ["negative momentum", [...words("3fe0000000000000 bfd0000000000000 3ff0000000000000"), ...left], "0 bfe032935512d09d 3fe1e6b6557697b2 bff7cbdcff9c38ec 3ff86526aa25a13a"],
];
const rejectedFlux = [];
for (const bad of special) for (let slot = 0; slot < 6; slot++) {
  const inputs = [...left, ...right]; inputs[slot] = bad;
  rejectedFlux.push(["nonfinite slot " + slot + " word " + bad.toString(16), inputs]);
}
const badStates = [
  ["zero density", [0n, 0n, one]],
  ["negative density", [one | sign, 0n, one]],
  ["energy below density", [one, 0n, one - 1n]],
  ["momentum outside domain", [one, one + 1n, two]],
  ["pressure underflow", [1n, 0n, 1n]],
  ["pressure ratio overflow", [1n, 0n, one]],
  ["enthalpy overflow", [one, 0n, max]],
  // https://github.com/lanyonai/CompressibleEuler/issues/2
  ["published cancellation", words("3ff3be3969ca97cb 41981433e88dacc6 432d5df2b6bc70d7")],
  // https://github.com/lanyonai/CompressibleEuler/issues/3
  ["published one-sided NaN", words("3fe999999999999a 400428f5c28f5c29 400fc083126e978d")],
];
for (const [label, state] of badStates) {
  rejectedFlux.push([label + " on left", [...state, ...left]]);
  rejectedFlux.push([label + " on right", [...left, ...state]]);
}
const large = [one, 0n, 0x7fe1ccf385ebc8a0n];
rejectedFlux.push(["viscosity overflow from accepted left", [...large, one, 0n, one]]);
rejectedFlux.push(["viscosity overflow from accepted right", [one, 0n, one, ...large]]);
const acceptedComponent = [
  ["constant", [one, one, one, one, one], [0n, one]],
  ["dissipation", [two, 0n, 0n, 0n, one], [0n, one | sign]],
  ["signed jump", [one, one, one | sign, one, one | sign], [0n, one]],
  ["smallest positive speed", [1n, 0n, 0n, 0n, one], [0n, 0n]],
];
const rejectedComponent = [
  ["zero speed", [0n, one, one, one, one]],
  ["negative zero speed", [sign, one, one, one, one]],
  ["negative speed", [one | sign, one, one, one, one]],
  ["flux sum overflow", [one, max, max, 0n, 0n]],
  ["state jump overflow", [one, 0n, 0n, max | sign, max]],
  ["viscosity overflow", [max, 0n, 0n, 0n, two]],
];
for (let slot = 0; slot < 5; slot++) {
  const inputs = [one, 0n, 0n, 0n, one]; inputs[slot] = 0x7ff8000000000000n;
  rejectedComponent.push(["NaN component input " + slot, inputs]);
}
function compile(output, entry, counts) {
  const wasm = path.join(output, entry + ".wasm"), watPath = path.join(output, entry + ".wat");
  const args = ["--module", moduleName, "--entry", moduleName + "." + entry];
  run([compiler, "compile", ...args, "--out", wasm]);
  run([compiler, "compile-wat", ...args, "--out", watPath]);
  const wat = fs.readFileSync(watPath, "utf8"), ir = run([compiler, "dump-ir", ...args]);
  for (const [op, count] of counts) {
    assert.equal(ir.split("f64" + op + "Bits").length - 1, count, entry + " IR " + op);
    assert.equal(wat.split("f64." + op.toLowerCase()).length - 1, count, entry + " WAT " + op);
  }
  return wasm;
}
function main() {
  const output = fs.mkdtempSync(path.join("tmp", "euler-dynamic-flux-"));
  const component = compile(output, "componentCheckedBits", [["Sub", 2], ["Mul", 3], ["Add", 1]]);
  const flux = compile(output, "fluxCheckedBits", [["Sub", 3], ["Div", 2], ["Mul", 8], ["Add", 4], ["Sqrt", 1]]);
  for (const [name, inputs, expected] of acceptedComponent)
    assert.deepEqual(callI64Slots(component, "componentCheckedBits", 2, inputs), expected, name);
  for (const [name, inputs] of rejectedComponent)
    assert.deepEqual(callI64Slots(component, "componentCheckedBits", 2, inputs), [1n, 0n], name);
  for (const [name, inputs, expected] of acceptedFlux)
    assert.deepEqual(callI64Slots(flux, "fluxCheckedBits", 5, inputs), words(expected), name);
  for (const [name, inputs] of rejectedFlux)
    assert.deepEqual(callI64Slots(flux, "fluxCheckedBits", 5, inputs), [1n, 0n, 0n, 0n, 0n], name);
  console.log("Checked " + (acceptedComponent.length + rejectedComponent.length) + " components and " +
    (acceptedFlux.length + rejectedFlux.length) + " dynamic interfaces; retained " + output);
}
try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
