#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.HeapLoops";
const directory = fs.mkdtempSync("tmp/heap-loops-");
runChecked(["lake", "build", "lean-wasm", moduleName]);
for (const entry of ["conditional", "initialAlias", "crossField"]) {
  const binary = path.join(directory, `${entry}.wasm`);
  runChecked([".lake/build/bin/lean-wasm", "compile", "--module", moduleName,
    "--entry", `${moduleName}.${entry}`, "--out", binary]);
  for (const count of [0, 1, 2, 5]) {
    for (const stop of [0, 1, 3, 8]) {
      const args = [host.i64(count), host.i64(stop)];
      if (entry === "conditional") {
        const successful = Math.min(count, stop);
        const expected = stop < count ? [] : [42, ...Array.from({ length: count }, (_, i) => i)];
        expected.push(...Array(successful).fill(99));
        const stats = host.callStats(binary, entry, "bytes", args);
        assert.deepEqual([...Buffer.from(stats.result, "hex")], expected, `${entry}(${count}, ${stop})`);
        assert.equal(stats.allocs - stats.frees, 1n,
          `${entry}(${count}, ${stop})`);
      } else {
        assert.equal(host.callI64(binary, entry, args),
          BigInt((entry === "initialAlias" ? 43 : 172) + Math.max(0, count - stop)));
        const stats = host.callStats(binary, entry, "i64", args);
        assert.equal(stats.allocs, stats.frees, `${entry}(${count}, ${stop})`);
      }
    }
  }
}
const foldBinary = path.join(directory, "conditionalFold.wasm");
runChecked([".lake/build/bin/lean-wasm", "compile", "--module", moduleName,
  "--entry", `${moduleName}.conditionalFold`, "--out", foldBinary]);
for (const input of [[], [0], [1], [1, 0, 2, 0, 3], [0, 0, 0]]) {
  const appended = input.filter(value => value !== 0);
  const stats = host.callStats(foldBinary, "conditionalFold", "array-u64",
    [host.arrayU64(input), host.arrayU64([42])]);
  assert.deepEqual(JSON.parse(stats.result), [42, ...appended]);
  assert.equal(stats.allocs - stats.frees, appended.length ? 3n : 2n,
    "only the borrowed inputs and any new folded result survive");
}
const aliasBinary = path.join(directory, "releaseAlias.wasm");
runChecked([".lake/build/bin/lean-wasm", "compile", "--module", moduleName,
  "--entry", `${moduleName}.releaseAlias`, "--out", aliasBinary]);
for (const replace of [0, 1, 2]) {
  const args = [host.i64(replace), host.arrayU64([7])];
  const stats = host.callStats(aliasBinary, "releaseAlias", "array-u64", args);
  assert.deepEqual(JSON.parse(stats.result), replace === 1 ? [9] : [8]);
  assert.equal(stats.allocs - stats.frees, 2n);
}
console.log("Checked heap loops, branch releases through aliases, and allocation counts");
