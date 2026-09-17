#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const wasm = path.join(root, "build/gelu-wide.wasm");

function word(value) {
  const bytes = Buffer.alloc(8);
  bytes.writeDoubleLE(value);
  return bytes.readBigUInt64LE();
}

function value(bits) {
  const bytes = Buffer.alloc(8);
  bytes.writeBigUInt64LE(bits);
  return bytes.readDoubleLE();
}

const inputs = [0n, word(-0), 1n, 0x8000000000000001n,
  ...[-8, -4, -3, -1, 1, 3, 4, 8].flatMap(x => [word(x)-1n, word(x), word(x)+1n]),
  ...[-7.9, -6, -5, -0.75, -0.25, 0.25, 0.75, 5, 6, 7.9, -100, 100].map(word),
  0x7FEFFFFFFFFFFFFFn, 0xFFEFFFFFFFFFFFFFn,
  word(Infinity), word(-Infinity), 0x7FF8000000000000n, 0xFFF8000000000000n];

function reference(x) {
  const a = Math.abs(x);
  const e = Math.exp(-2*Math.sqrt(2/Math.PI)*(a+0.044715*a*a*a));
  return x >= 0 ? a/(1+e) : -a*e/(1+e);
}

function main() {
  runChecked(["lake", "--log-level=error", "build", "Project.GeluWide.Model"],
    { cwd: proofRoot, encoding: "utf8" });
  runChecked(["lake", "env", path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", "Project.GeluWide.Model", "--entry", "Project.GeluWide.geluWide", "--out", wasm],
    { cwd: proofRoot, encoding: "utf8" });
  const native = runChecked(["lake", "env", "lean", "--run", "Project/GeluWide/NativeTest.lean",
    ...inputs.map(String)], { cwd: proofRoot, encoding: "utf8", timeout: 120000 }).stdout.trim()
    .split(/\r?\n/).map(line => line.split(/\s+/).map(BigInt));
  assert.equal(native.length, inputs.length);
  let maximumError = 0;
  for (const [i, input] of inputs.entries()) {
    const result = callI64Slots(wasm, "geluWide", 2, [input]);
    assert.deepEqual(result, native[i], `Native bit model differs for ${input}`);
    const x = value(input);
    if (!Number.isFinite(x)) {
      assert.deepEqual(result, [1n, 0n]);
      continue;
    }
    assert.equal(result[0], 0n);
    if (Math.abs(x) > 8) {
      assert.equal(result[1], x > 0 ? input : 0n);
    } else {
      const y = value(result[1]);
      assert(Number.isFinite(y));
      const expected = reference(x);
      const error = Math.abs(y-expected);
      maximumError = Math.max(maximumError, error);
      assert(error <= 2e-14*Math.abs(expected)+Number.MIN_VALUE,
        `GELU comparison differs at ${x}: ${y} versus ${expected}`);
    }
  }
  process.stdout.write(`Checked ${inputs.length} GELU WASM results against the native bit model; ` +
    `maximum empirical absolute error ${maximumError}\n`);
}

main();
