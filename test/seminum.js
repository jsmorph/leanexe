#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runExample, invoke } = require("../tools/seminum");
const { runChecked, spawnResult } = require("../tools/run-process");
const catalog = require("../libraries/catalog.json");

const root = path.resolve(__dirname, "..");
const options = { cwd: root, encoding: "utf8", timeout: 120000 };
const max = (1n << 64n) - 1n;
const cases = [];
function add(command, args, result) { cases.push({ command, args: args.map(String), result }); }
function gcd(a, b) { while (b !== 0n) [a, b] = [b, a % b]; return a; }
function polynomial(x, coefficients) {
  return coefficients.reduce((sum, coefficient, degree) => sum + coefficient * x ** BigInt(degree), 0n);
}

for (const [a, b] of [[0n, 0n], [0n, max], [max, 0n], [48n, 18n], [1n, max],
  [max, max], [max, max - 1n], [12200160415121876738n, 7540113804746346429n]]) {
  add("gcd", [a, b], `ok ${gcd(a, b)}`);
}
for (const [n, d] of [[0n, 7n], [48n, 18n], [max, max], [max, 1n], [7n, 0n]]) {
  const divisor = gcd(n, d);
  add("fraction", [n, d], d === 0n ? "error 1" : `ok ${n / divisor}/${d / divisor}`);
}
for (const [x, cs] of [[0n, []], [max, []], [max, [7n]], [2n, [1n, 3n, 2n]],
  [0n, [max, max, max]], [1n, [max]], [1n, [max, 1n]], [max, [0n, 1n]],
  [max, [0n, 2n]], [max, [max, 0n, 0n]], [2n, [max - 2n, 1n]]]) {
  const value = polynomial(x, cs);
  add("polynomial", [x, cs.length ? cs.join(",") : "[]"], value > max ? "error 2" : `ok ${value}`);
}
for (let i = 0n; i < 24n; i++) {
  const a = (i * 6364136223846793005n + 1442695040888963407n) & max;
  const b = (i * 2862933555777941757n + 3037000493n) & max;
  add("gcd", [a, b], `ok ${gcd(a, b)}`);
  const x = i % 7n;
  const cs = [i, 2n * i + 1n, 3n, i % 5n];
  add("polynomial", [x, cs.join(",")], `ok ${polynomial(x, cs)}`);
}
add("ratio", [2, "1,3,2", "2,2"], "ok 5/2");
add("ratio", [2, "[]", "2,2"], "ok 0/1");
add("ratio", [2, "1", "[]"], "error 1");
add("ratio", [2, `${max},1`, "1"], "error 2");
add("ratio", [2, "1", `${max},1`], "error 2");

for (let shift = 0n; shift < 64n; shift += 7n) {
  add("gcd", [1n << shift, max], "ok 1");
  add("gcd", [1n << shift, 1n << shift], `ok ${1n << shift}`);
}
for (const item of [...cases]) {
  if (item.command === "gcd" || item.command === "fraction") {
    add(`${item.command}-binary`, item.args, item.result);
  }
}

function bits(value) {
  const buffer = Buffer.alloc(8);
  buffer.writeDoubleLE(value);
  return buffer.readBigUInt64LE();
}
function value(word) {
  const buffer = Buffer.alloc(8);
  buffer.writeBigUInt64LE(word);
  return buffer.readDoubleLE();
}

function main() {
  for (const item of cases) {
    let actual;
    try { actual = `ok ${runExample(item.command, item.args)}`; }
    catch (error) {
      if (!(error instanceof RangeError)) throw error;
      if (error.message === "denominator must be positive") actual = "error 1";
      else if (error.message === "arithmetic overflow") actual = "error 2";
      else throw error;
    }
    assert.equal(actual, item.result, `${item.command} ${item.args.join(" ")}`);
  }
  const nativeArgs = cases.map(item => [item.command, ...item.args].join(":"));
  const expected = cases.map(item => item.result);
  const specialWords = [0n, 1n, 0x8000000000000000n, 0x8000000000000001n,
    0x7ff0000000000000n, 0xfff0000000000000n, 0x7ff8000000000001n,
    0xfff8000000000001n, 0x7ff0000000000001n, 0xfff0000000000001n,
    bits(-1) - 1n, bits(-1), bits(-1) + 1n, bits(1) - 1n, bits(1), bits(1) + 1n];
  let maximumError = 0;
  let floatCases = 0;
  for (const name of ["exponential", "decay"]) {
    const words = [...specialWords, ...Array.from({ length: 33 }, (_, i) => bits((name === "decay" ? i : -i) / 32))];
    for (const word of words) {
      const x = value(word);
      const admitted = Number.isFinite(x) && (name === "decay" ? x >= 0 && x <= 1 : x >= -1 && x <= 0);
      const [status, result] = invoke(name, 2, [`i64:${word}`]);
      assert.equal(status, admitted ? 0n : name === "decay" ? 4n : 3n, `${name} ${word.toString(16)}`);
      if (admitted) {
        assert.ok(Number.isFinite(value(result)) && value(result) > 0);
        const error = Math.abs(value(result) - Math.exp(name === "decay" ? -x : x));
        maximumError = Math.max(maximumError, error);
        assert.ok(error <= 1 / 4000, `absolute error ${error} at ${x}`);
        if (x === 0) assert.equal(result, bits(1));
      } else {
        assert.equal(result, 0n);
      }
      nativeArgs.push(`${name === "decay" ? "decay" : "exp"}-word:${word}`);
      expected.push(status === 0n ? `ok ${result}` : `error ${status}`);
      floatCases++;
    }
  }
  const native = runChecked(["lake", "env", "lean", "--run", "test/SeminumNative.lean",
    ...nativeArgs], options).stdout.trim().split("\n");
  assert.deepEqual(native, expected);

  const components = JSON.parse(fs.readFileSync(path.join(root, "build/seminum/components.json"), "utf8"));
  assert.equal(components.length, catalog.length);
  assert.deepEqual(new Set(components.map(item => item.id)), new Set(catalog.map(item => item.id)));
  const cli = [path.join(root, "tools/seminum")];
  assert.equal(runChecked([...cli, "fraction", "48", "18"], options).stdout, "8/3\n");
  assert.equal(runChecked([...cli, "fraction-binary", "48", "18"], options).stdout, "8/3\n");
  assert.equal(runChecked([...cli, "decay", "0.5"], options).stdout, "0.6065321180555556\n");
  assert.equal(runChecked([...cli, "exp-taylor6-bits", "bfe0000000000000"], options).stdout, "3fe368b60b60b60c\n");
  for (const args of [[], ["gcd", "-1", "2"], ["gcd", `${max + 1n}`, "2"],
    ["fraction", "1", "0"], ["polynomial", "2", "1,,2"],
    ["polynomial", "2", `${max},1`], ["exp-taylor6", "0.1"], ["exp-taylor6", "-1.01"],
    ["exp-taylor6", "NaN"], ["exp-taylor6", "1e999"], ["exp-taylor6-bits", "fff0000000000000"],
    ["decay", "-0.1"], ["decay", "1.01"]]) {
    const result = spawnResult([...cli, ...args], options);
    assert.equal(result.status, 2, args.join(" "));
    assert.equal(result.stdout, "");
    assert.match(result.stderr, /^seminum: /);
  }
  process.stdout.write(`Passed ${cases.length + floatCases} WASM/native comparisons, mathematical references, component discovery, and CLI errors\n`);
  process.stdout.write(`Maximum sampled exponential absolute error: ${maximumError}\n`);
}

try { main(); }
catch (error) { process.stderr.write(`${error.stack}\n`); process.exitCode = 1; }
