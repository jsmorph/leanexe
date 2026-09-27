"use strict";

const assert = require("node:assert/strict");
const { ensureHost } = require("../tools/wasmtime-host");
const { runChecked } = require("../tools/run-process");
const beck = require("../tools/beck-exact");
const wide = require("../data/beck/exact-overlap.json");
const wideOnly = process.argv.length === 3 && process.argv[2] === "--wide";
if (process.argv.length > 2 && !wideOnly) throw new Error("usage: node test/beck_exact.js [--wide]");

const cases = [];
function valid(input) { cases.push({ input, words: beck.encode(input), status: 0 }); }
for (let jobs = 0; jobs <= 3; jobs++) {
  for (let code = 0; code < 8 ** jobs; code++) {
    let digits = code;
    valid({ categories: 3, jobs: Array.from({ length: jobs }, () => {
      const row = [0, 1, 2].filter(category => digits & (1 << category));
      digits = Math.floor(digits / 8);
      return row;
    }) });
  }
}
valid(require("../data/beck/overlap.json"));
valid(wide);
valid({ categories: 0, jobs: Array.from({ length: 32 }, () => []) });
valid({ categories: 20, jobs: [] });
valid({ categories: 12, jobs: Array.from({ length: 15 }, () => [0, 11]) });
let seed = 76231;
function next(n) { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return (seed >>> 8) % n; }
for (const count of [6, 12, 24]) {
  for (let trial = 0; trial < 4; trial++) {
    valid({ categories: 6, jobs: Array.from({ length: count }, () => {
      const a = next(6), b = next(6);
      return a === b ? [a] : [a, b];
    }) });
  }
}
for (const words of [[], [0], [0, 0, 0], [1, 1], [1, 1, 1, 1], [1, 2, 2, 0, 0]]) cases.push({ words, status: 1 });
cases.push({ words: [1, "18446744073709551615", 0], status: 2 });
if (wideOnly) {
  cases.length = 0;
  for (const count of [24, 32, 40, 48, 64]) valid({ categories: wide.categories, jobs: wide.jobs.slice(0, count) });
}

beck.prepare();
const native = runChecked(["lake", "env", "lean", "--run", "test/BeckExactNative.lean"], {
  cwd: beck.root, encoding: "utf8", timeout: 120000,
  input: cases.map(test => test.words.join(",")).join("\n") + "\n",
}).stdout.trim().split("\n").map(line => JSON.parse(line));
assert.equal(native.length, cases.length);
let slowest = 0;
for (const [index, test] of cases.entries()) {
  const began = performance.now();
  let result;
  if (wideOnly) {
    process.stdout.write(`Testing ${test.input.jobs.length} jobs and ${test.input.categories} categories\n`);
    const measured = runChecked([ensureHost(), "call-stats",
      beck.wasm, "compute", "array-u64", `array-u64:${test.words.join(",")}`],
      { cwd: beck.root, encoding: "utf8", timeout: 60000 });
    const [words, stats] = measured.stdout.trim().split("\n");
    result = JSON.parse(words);
    process.stdout.write(`${stats}\nelapsed-ms ${(performance.now() - began).toFixed(1)}\n`);
  } else result = beck.execute(test.words);
  slowest = Math.max(slowest, performance.now() - began);
  assert.deepEqual(result, native[index], `native/WASM case ${index}`);
  assert.equal(result[0], test.status, `status case ${index}: ${JSON.stringify(test.input)}`);
  if (test.status === 0) assert.equal(beck.check(test.input, result).status, "ok");
}
console.log(`beck exact: ${cases.length} native/WASM comparisons and output checks passed; slowest process invocation ${slowest.toFixed(1)} ms`);
