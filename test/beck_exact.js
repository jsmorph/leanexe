"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const crypto = require("node:crypto");
const { ensureHost } = require("../tools/wasmtime-host");
const { runChecked } = require("../tools/run-process");
const beck = require("../tools/beck-exact");
const wide = require("../data/beck/exact-overlap.json");
const mode = process.argv[2];
if (process.argv.length > 3 || (mode && !["--wide", "--memory", "--stress"].includes(mode))) {
  throw new Error("usage: node test/beck_exact.js [--wide|--memory|--stress]");
}

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
if (mode) {
  cases.length = 0;
  if (mode === "--stress") valid(require("../data/beck/exact-256.json"));
  else {
    for (const count of [24, 32, 40, 48, 64]) valid({ categories: wide.categories, jobs: wide.jobs.slice(0, count) });
    if (mode === "--memory") {
      for (const [count, categories, overlap] of [[64, 8, 3], [128, 8, 3], [128, 4, 2]]) {
        seed = 38117;
        valid({ categories, jobs: Array.from({ length: count }, () => {
          const row = new Set();
          while (row.size < overlap) row.add(next(categories));
          return [...row].sort((a, b) => a - b);
        }) });
      }
    }
  }
}

beck.prepare();
if (mode) console.log(`sha256 ${crypto.createHash("sha256").update(fs.readFileSync(beck.wasm)).digest("hex")}`);
const native = runChecked(["lake", "env", "lean", "--run", "test/BeckExactNative.lean"], {
  cwd: beck.root, encoding: "utf8", timeout: 120000,
  input: cases.map(test => test.words.join(",")).join("\n") + "\n",
}).stdout.trim().split("\n").map(line => JSON.parse(line));
assert.equal(native.length, cases.length);
let slowest = 0;
for (const [index, test] of cases.entries()) {
  const began = performance.now();
  let result;
  if (mode) {
    process.stdout.write(`Testing ${test.input.jobs.length} jobs and ${test.input.categories} categories\n`);
    const script = [`alloc 0 ${8 + 8 * test.words.length}`, `write-u64 0 0 ${test.words.length}`];
    test.words.forEach((word, i) => script.push(`write-u64 0 ${8 + 8 * i} ${word}`));
    script.push("arg-ptr 0", "memory-size", "call compute 1", "stats", "memory-size",
      `read-memory result:0 ${8 * (test.input.jobs.length + 3)}`, "done");
    const measured = runChecked([ensureHost(), "script", beck.wasm], {
      cwd: beck.root, encoding: "utf8", timeout: 60000, input: script.join("\n") + "\n",
    }).stdout.trim().split("\n");
    const memory = measured.find(line => line.startsWith("memory "));
    assert.ok(memory, "missing output memory");
    const bytes = Buffer.from(memory.split(" ")[3], "hex");
    const length = Number(bytes.readBigUInt64LE(0));
    assert.ok(length <= test.input.jobs.length + 2, "unexpected output size");
    result = Array.from({ length }, (_, i) => Number(bytes.readBigUInt64LE(8 + 8 * i)));
    const sizes = measured.filter(line => line.startsWith("memory-size ")).map(line => Number(line.split(" ")[1]));
    assert.equal(sizes.length, 2, "missing memory measurements");
    const stats = measured.find(line => line.startsWith("stats "));
    assert.ok(stats, "missing allocation counters");
    console.log(JSON.stringify({ jobs: test.input.jobs.length, categories: test.input.categories,
      memoryBytes: sizes, elapsedMs: +(performance.now() - began).toFixed(1), stats }));
  } else result = beck.execute(test.words);
  slowest = Math.max(slowest, performance.now() - began);
  assert.deepEqual(result, native[index], `native/WASM case ${index}`);
  assert.equal(result[0], test.status, `status case ${index}: ${JSON.stringify(test.input)}`);
  if (test.status === 0) assert.equal(beck.check(test.input, result).status, "ok");
}
console.log(`beck exact: ${cases.length} native/WASM comparisons and output checks passed; slowest process invocation ${slowest.toFixed(1)} ms`);
