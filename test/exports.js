#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked, spawnResult } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.Exports";
const compiler = ".lake/build/bin/lean-wasm";
const directory = fs.mkdtempSync("tmp/exports-");
const binary = path.join(directory, "exports.wasm");
runChecked(["lake", "build", "lean-wasm", moduleName]);
const names = ["wordIncrement", "wordDouble", "appendByte", "appendTwice", "borrow", "increment"];
const entries = names.map(name => `${moduleName}.${name}`).join(",");
runChecked([compiler, "compile", "--module", moduleName, "--entries", entries, "--out", binary]);

assert.equal(host.callI64(binary, "increment", [host.i64(0x1ffffffffn)]), 0n);
assert.equal(host.callI64(binary, "wordIncrement", [host.i64(0xffffffffffffffffn)]), 0n);
assert.equal(host.callI64(binary, "wordDouble", [host.i64(21)]), 42n);
for (const [entry, expected] of [["appendByte", [1, 2, 255]], ["appendTwice", [1, 2, 255, 0]],
  ["borrow", [1, 2]]]) {
  const args = [host.byteArray(Buffer.from([1, 2]))];
  if (entry !== "borrow") args.push(host.i64(511));
  const stats = host.callStats(binary, entry, "slots:2", args);
  assert.equal(stats.allocs - stats.frees, entry === "borrow" ? 1n : 2n);
  const setup = ["bytes 0 0102", "arg-ptr 0", "arg-u64 2"];
  if (entry !== "borrow") setup.push("arg-u64 511");
  const result = host.script(binary, setup, entry, 2, ["read-memory result:0 result:1"]);
  assert.deepEqual([...result.memoryChunks[0].bytes], expected);
}
for (const entries of [`${moduleName}.appendByte,${moduleName}.appendByte`, ""]) {
  const result = spawnResult([compiler, "compile", "--module", moduleName,
    "--entries", entries, "--out", binary], { encoding: "utf8" });
  assert.equal(result.status, 3);
  assert.match(result.stderr, entries ? /duplicate entry export name/ : /names must be nonempty/);
}
console.log("Checked multiple exports, shared calls, narrow words, borrowed results, and ownership");
