#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");
const moduleName = "LeanExe.Examples.EulerCellStep";
const compiler = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const run = args => runChecked(args, { encoding: "utf8", timeout: 120000 }).stdout;
const words = text => text.split(" ").map(x => BigInt("0x" + x));
const one = 0x3ff0000000000000n, two = 0x4000000000000000n;
const quarter = 0x3fd0000000000000n, sign = 0x8000000000000000n, max = 0x7fefffffffffffffn;
const left = words("3ff0000000000000 0 4004000000000000");
const right = words("3fc0000000000000 0 3fd0000000000000");
const uniform = [one, one, one];
// Frozen host IEEE comparisons are regression evidence, separate from Lean proofs.
const acceptedCell = [
  ["uniform left", [quarter, ...left, ...left, ...left], "0 3ff0000000000000 0 4004000000000000 3ff0000000000000 3ff2ee73dadc9b57 3fd2ee73dadc9b57"],
  ["left interface", [quarter, ...left, ...left, ...right], "0 3febdbd6a81fbe05 3fbccccccccccccc 40015677b538fa28 3feba5bacf768c05 3ff2ee73dadc9b57 3fd2ee73dadc9b57"],
  ["right interface", [quarter, ...left, ...right, ...right], "0 3fd04852afc083f6 3fbcccccccccccce 3fe2a6212b1c1761 3fcc90967b850068 3ff2ee73dadc9b57 3fd2ee73dadc9b57"],
  ["uniform right", [quarter, ...right, ...right, ...right], "0 3fc0000000000000 0 3fd0000000000000 3fb999999999999a 3ff0eecc87dbfa54 3fd0eecc87dbfa54"],
  ["CFL ceiling", [0x3fdb0b80ef844ba1n, ...left, ...right, ...right], "0 3fd6000000000000 3fc857273df710df 3fea000000000000 3fd3741900662250 3ff2ee73dadc9b57 3fe0000000000000"],
  ["adjacent ratio still rounds to ceiling", [0x3fdb0b80ef844ba2n, ...left, ...right, ...right], "0 3fd6000000000000 3fc857273df710e0 3fea000000000001 3fd3741900662250 3ff2ee73dadc9b57 3fe0000000000000"],
  ["moving domain boundary", [quarter, ...uniform, ...uniform, ...uniform], "0 3ff0000000000000 3ff0000000000000 3ff0000000000000 3fc999999999999a 3ff8776643edfd2a 3fd8776643edfd2a"],
  ["smallest positive ratio", [1n, ...left, ...left, ...left], "0 3ff0000000000000 0 4004000000000000 3ff0000000000000 3ff2ee73dadc9b57 1"],
];
const rejectedCell = [];
for (const ratio of [0n, sign, one | sign, 0x7ff0000000000000n, 0xfff0000000000000n,
    0x7ff8000000000000n, max, 0x3fe0000000000000n, 0x3fdb0b80ef844ba3n])
  rejectedCell.push(["bad or excessive ratio " + ratio.toString(16), [ratio, ...left, ...right, ...right]]);
const badStates = [
  ["NaN state", [one, 0x7ff8000000000000n, one]],
  ["published cancellation", words("3ff3be3969ca97cb 41981433e88dacc6 432d5df2b6bc70d7")],
  ["published one-sided NaN", words("3fe999999999999a 400428f5c28f5c29 400fc083126e978d")],
];
for (const [name, state] of badStates) for (let slot = 0; slot < 3; slot++) {
  const cells = [left, left, left]; cells[slot] = state;
  rejectedCell.push([name + " neighborhood slot " + slot, [quarter, ...cells.flat()]]);
}
rejectedCell.push(["updated energy below density despite valid incoming states and CFL",
  [quarter, one, 0n, one, one, 0n, one, ...uniform]]);
const acceptedUpdate = [
  ["constant flux", [quarter, one, one, one], [0n, one]],
  ["positive flux difference", [quarter, one, 0n, one], words("0 3fe8000000000000")],
  ["negative flux difference", [quarter, one, one, 0n], words("0 3ff4000000000000")],
  ["subnormal ratio", [1n, one, 0n, one], [0n, one]],
  ["negative zero state", [quarter, sign, 0n, 0n], [0n, sign]],
];
const rejectedUpdate = [
  ["zero ratio", [0n, one, 0n, one]],
  ["negative zero ratio", [sign, one, 0n, one]],
  ["negative ratio", [one | sign, one, 0n, one]],
  ["infinite ratio", [0x7ff0000000000000n, one, 0n, one]],
  ["flux difference overflow", [quarter, one, max | sign, max]],
  ["increment overflow", [max, one, 0n, two]],
  ["final subtraction overflow", [one, max | sign, 0n, max]],
];
for (let slot = 0; slot < 4; slot++) {
  const args = [quarter, one, 0n, one]; args[slot] = 0x7ff8000000000000n;
  rejectedUpdate.push(["NaN update input " + slot, args]);
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
  const output = fs.mkdtempSync(path.join("tmp", "euler-cell-step-"));
  const update = compile(output, "updateCheckedBits", [["Sub", 2], ["Mul", 1]]);
  const cell = compile(output, "cellCheckedBits", [["Sub", 5], ["Div", 2], ["Mul", 10], ["Add", 4], ["Sqrt", 1]]);
  for (const [name, inputs, expected] of acceptedUpdate)
    assert.deepEqual(callI64Slots(update, "updateCheckedBits", 2, inputs), expected, name);
  for (const [name, inputs] of rejectedUpdate)
    assert.deepEqual(callI64Slots(update, "updateCheckedBits", 2, inputs), [1n, 0n], name);
  for (const [name, inputs, expected] of acceptedCell)
    assert.deepEqual(callI64Slots(cell, "cellCheckedBits", 7, inputs), words(expected), name);
  for (const [name, inputs] of rejectedCell)
    assert.deepEqual(callI64Slots(cell, "cellCheckedBits", 7, inputs), [1n, 0n, 0n, 0n, 0n, 0n, 0n], name);
  console.log("Checked " + (acceptedUpdate.length + rejectedUpdate.length) + " scalar updates and " +
    (acceptedCell.length + rejectedCell.length) + " cell updates; retained " + output);
}
try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
