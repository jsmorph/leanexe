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
console.log("Checked conditional heap loops, failure branches, initial aliases, and allocation counts");
