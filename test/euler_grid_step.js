#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");
const moduleName = "LeanExe.Examples.EulerGridStep";
const compiler = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const run = args => runChecked(args, { encoding: "utf8", timeout: 120000 }).stdout;
const words = text => text.split(" ").map(x => BigInt("0x" + x));
const one = 0x3ff0000000000000n, quarter = 0x3fd0000000000000n, sign = 0x8000000000000000n;
const left = words("3ff0000000000000 0 4004000000000000");
const right = words("3fc0000000000000 0 3fd0000000000000");
const moving = [one, one, one];
const sod100 = [...Array.from({length:50}, () => left), ...Array.from({length:50}, () => right)].flat();
// Fixed independently evaluated words, also checked at the scalar cell boundary.
const leftConstant = words("3ff0000000000000 0 4004000000000000 3ff0000000000000 3ff2ee73dadc9b57 3fd2ee73dadc9b57");
const rightConstant = words("3fc0000000000000 0 3fd0000000000000 3fb999999999999a 3ff0eecc87dbfa54 3fd0eecc87dbfa54");
const leftInterface = words("3febdbd6a81fbe05 3fbccccccccccccc 40015677b538fa28 3feba5bacf768c05 3ff2ee73dadc9b57 3fd2ee73dadc9b57");
const rightInterface = words("3fd04852afc083f6 3fbcccccccccccce 3fe2a6212b1c1761 3fcc90967b850068 3ff2ee73dadc9b57 3fd2ee73dadc9b57");
const movingConstant = words("3ff0000000000000 3ff0000000000000 3ff0000000000000 3fc999999999999a 3ff8776643edfd2a 3fd8776643edfd2a");
const accepted = [
  ["single left cell", left, [0n, ...leftConstant]],
  ["single right cell", right, [0n, ...rightConstant]],
  ["two-cell Sod", [...left, ...right], [0n, ...leftInterface, ...rightInterface]],
  ["100-cell Sod", sod100, [0n, ...Array.from({length:49}, () => leftConstant).flat(), ...leftInterface, ...rightInterface, ...Array.from({length:49}, () => rightConstant).flat()]],
  ["moving uniform grid", [...moving, ...moving], [0n, ...movingConstant, ...movingConstant]],
];
const shapes = [[], [one], [one, one], [one, one, one, one]];
const invalidStates = [
  ["NaN first state", [one, 0x7ff8000000000000n, one, ...left]],
  ["published cancellation last", [...left, ...words("3ff3be3969ca97cb 41981433e88dacc6 432d5df2b6bc70d7")]],
  ["published one-sided NaN first", [...words("3fe999999999999a 400428f5c28f5c29 400fc083126e978d"), ...left]],
];
function arrayResult(wasm, ratio, grid) {
  const text = host.call(wasm, "stepCheckedBits", "array-u64", [host.i64(ratio), host.arrayU64(grid)]);
  assert.match(text, /^\[(?:[0-9]+(?:, [0-9]+)*)?\]$/);
  return text.slice(1, -1).split(", ").filter(Boolean).map(BigInt);
}
function speedResult(wasm, grid) {
  const text = host.call(wasm, "maxSpeedCheckedBits", "slots:2", [host.arrayU64(grid)]);
  assert.match(text, /^[0-9]+ [0-9]+$/);
  return text.split(" ").map(BigInt);
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
  const output = fs.mkdtempSync(path.join("tmp", "euler-grid-step-"));
  const scan = compile(output, "maxSpeedCheckedBits", [["Sub", 1], ["Div", 2], ["Mul", 5], ["Add", 3], ["Sqrt", 1]]);
  const step = compile(output, "stepCheckedBits", [["Sub", 5], ["Div", 2], ["Mul", 10], ["Add", 4], ["Sqrt", 1]]);
  let checks = 0;
  for (const [name, grid, expected] of accepted) {
    assert.deepEqual(arrayResult(step, quarter, grid), expected, name); checks++;
    const speed = name.includes("moving") ? 0x3ff8776643edfd2an : name.includes("right cell") ? 0x3ff0eecc87dbfa54n : 0x3ff2ee73dadc9b57n;
    assert.deepEqual(speedResult(scan, grid), [0n, speed], name + " speed"); checks++;
  }
  for (const grid of shapes) {
    assert.deepEqual(arrayResult(step, quarter, grid), [1n], "malformed grid"); checks++;
    assert.deepEqual(speedResult(scan, grid), [1n, 0n], "malformed speed grid"); checks++;
  }
  for (const ratio of [0n, sign, one | sign, 0x7ff8000000000000n]) {
    assert.deepEqual(arrayResult(step, ratio, left), [1n], "invalid ratio"); checks++;
  }
  for (const [name, grid] of invalidStates) {
    assert.equal(arrayResult(step, quarter, grid)[0], 1n, name); checks++;
    assert.deepEqual(speedResult(scan, grid), [1n, 0n], name + " speed"); checks++;
  }
  for (const ratio of [0x3fe0000000000000n, 0x7fefffffffffffffn]) {
    assert.equal(arrayResult(step, ratio, [...left, ...right])[0], 1n, "CFL rejection"); checks++;
  }
  assert.equal(arrayResult(step, quarter, [one, 0n, one, one, 0n, one, ...moving])[0], 1n, "final state rejection"); checks++;
  console.log("Checked " + checks + " grid/scan cases including the 100-cell initial step; retained " + output);
}
try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
