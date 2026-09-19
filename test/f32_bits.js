#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked, spawnResult } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.Float32Bits";
const compiler = process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm";
const run = args => runChecked(args, { encoding: "utf8" }).stdout.trim();
const one = 0x3f800000n, two = 0x40000000n, negZero = 0x80000000n;
const inf = 0x7f800000n, nan = 0x7fc00000n, max = 0x7f7fffffn;
const vectors = {
  addBits: [
    [[one, one], two], [[negZero, negZero], negZero], [[negZero, 0n], 0n],
    [[one, 0x33800000n], one], [[one + 1n, 0x33800000n], one + 2n],
    [[1n, 1n], 2n], [[0x7fffffn, 1n], 0x800000n],
    [[max, max], inf], [[inf, inf | negZero], "nan"], [[nan, one], "nan"],
  ],
  subBits: [
    [[one, one], 0n], [[negZero, 0n], negZero], [[0n, negZero], 0n],
    [[0x800000n, 0x7fffffn], 1n], [[one, one - 1n], 0x33800000n],
    [[inf, inf], "nan"], [[one, nan], "nan"],
  ],
  mulBits: [
    [[one, two], two], [[negZero, two], negZero], [[negZero, negZero], 0n],
    [[0x800000n, 0x3f000000n], 0x400000n], [[1n, 0x3f000000n], 0n],
    [[3n, 0x3f000000n], 2n], [[max, two], inf], [[0n, inf], "nan"],
  ],
  divBits: [
    [[one, two], 0x3f000000n], [[one, 0x40400000n], 0x3eaaaaabn],
    [[one, negZero], inf | negZero], [[negZero, one], negZero],
    [[0x800000n, two], 0x400000n], [[1n, two], 0n], [[3n, two], 2n],
    [[0n, 0n], "nan"], [[inf, inf], "nan"], [[nan, one], "nan"],
  ],
  sqrtBits: [
    [[0n], 0n], [[negZero], negZero], [[0x40800000n], two],
    [[two], 0x3fb504f3n], [[0x800000n], 0x20000000n],
    [[one | negZero], "nan"], [[inf], inf], [[nan], "nan"],
  ],
  toFloat64Bits: [
    [[one], 0x3ff0000000000000n], [[negZero], 0x8000000000000000n],
    [[1n], 0x36a0000000000000n], [[max], 0x47efffffe0000000n],
    [[inf], 0x7ff0000000000000n], [[nan], "nan"],
  ],
  ofFloat64Bits: [
    [[0x3ff0000000000000n], one], [[0x8000000000000000n], negZero],
    [[0x3ff0000010000000n], one], [[0x3ff0000030000000n], one + 2n],
    [[0x36a0000000000000n], 1n], [[0x3690000000000000n], 0n],
    [[0x47efffffe0000000n], max], [[0x47f0000000000000n], inf],
    [[0x7ff8000000000000n], "nan"],
  ],
  mulThenAddBits: [
    [[one, two, one], 0x40400000n],
    [[one + 1n, one - 2n, one | negZero], 0n],
  ],
  sqrtDivBits: [[[0x41100000n, 0x40800000n], 0x3fc00000n]],
  roundTripBits: [[ [1n], 1n], [[max], max], [[negZero], negZero]],
};

for (const value of [0x7f800001n, 0xffc12345n]) {
  for (const entry of ["addBits", "subBits", "mulBits", "divBits"])
    vectors[entry].push([[value, one], "nan"], [[one, value], "nan"]);
  vectors.sqrtBits.push([[value], "nan"]);
  vectors.toFloat64Bits.push([[value], "nan"]);
}
for (const value of [0x7ff0000000000001n, 0xfff8123456789abcn])
  vectors.ofFloat64Bits.push([[value], "nan"]);

function checkResult(actual, expected, entry, label) {
  if (expected !== "nan") {
    assert.equal(actual, expected, `${label}: ${entry}`);
    return;
  }
  const wide = entry === "toFloat64Bits";
  if (label === "Wasmtime") {
    assert.equal(actual, wide ? 0x7ff8000000000000n : nan, `${entry}: canonical NaN bits`);
    return;
  }
  const exponent = wide ? 0x7ff0000000000000n : inf;
  const fraction = wide ? 0xfffffffffffffn : 0x7fffffn;
  assert.equal(actual & exponent, exponent, `${label}: NaN exponent`);
  assert.notEqual(actual & fraction, 0n, `${label}: NaN fraction`);
}

function main() {
  run(["lake", "build", "lean-wasm", moduleName]);
  run(["tools/build-wasmtime-host.sh"]);
  fs.mkdirSync("tmp", { recursive: true });
  const output = fs.mkdtempSync(path.join("tmp", "f32-bits-"));
  const nativeSource = path.join(output, "Reference.lean");
  const cases = Object.entries(vectors).flatMap(([entry, rows]) =>
    rows.map(([inputs, expected]) => ({ entry, inputs, expected })));
  fs.writeFileSync(nativeSource, `import ${moduleName}\n` + cases.map(({ entry, inputs }) =>
    `#eval (${moduleName}.${entry} ${inputs.join(" ")}).toNat\n`).join(""));
  const native = run(["lake", "env", "lean", nativeSource]).split(/\r?\n/).map(BigInt);
  assert.equal(native.length, cases.length);
  cases.forEach(({ entry, expected }, i) => checkResult(native[i], expected, entry, "Lean"));

  for (const [entry, rows] of Object.entries(vectors)) {
    const args = ["--module", moduleName, "--entry", `${moduleName}.${entry}`];
    const wasm = path.join(output, `${entry}.wasm`);
    const wat = path.join(output, `${entry}.wat`);
    run([compiler, "compile", ...args, "--out", wasm]);
    run([compiler, "compile-wat", ...args, "--out", wat]);
    const text = fs.readFileSync(wat, "utf8");
    assert.match(text, /f32\./);
    assert.match(run([compiler, "report", ...args]), /binary32 bit-pattern floating-point intrinsic/);
    const image = path.join(output, `${entry}.image`);
    const imageResult = spawnResult([compiler, "compile-image", ...args, "--out", image],
      { encoding: "utf8" });
    assert.notEqual(imageResult.status, 0);
    assert.match(imageResult.stderr, /image schema v2/);
    assert.equal(fs.existsSync(image), false);
    if (entry === "mulThenAddBits") {
      assert.match(text, /f32\.mul/);
      assert.match(text, /f32\.add/);
    }
    for (const [inputs, expected] of rows) {
      const actual = host.callI64(wasm, entry, inputs.map(host.i64));
      checkResult(actual, expected, entry, "Wasmtime");
      const ir = BigInt(run([compiler, "eval-ir", ...args, ...inputs.map(String)]));
      checkResult(ir, expected, entry, "IR");
    }
  }
  const mapped = path.join(output, "shiftBits.wasm");
  run([compiler, "compile", "--module", moduleName, "--entry", `${moduleName}.shiftBits`,
    "--out", mapped]);
  const shifted = JSON.parse(host.call(mapped, "shiftBits", "array-u64",
    [host.arrayU64([0n, one, two]), host.i64(one)])).map(BigInt);
  assert.deepEqual(shifted, [one, two, 0x40400000n]);
  process.stdout.write(`Checked ${cases.length} FP32 cases in Lean, IR, and Wasmtime, and an array map\n`);
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
