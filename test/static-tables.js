#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked, spawnResult } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.StaticTables";
const compiler = ".lake/build/bin/lean-wasm";
const directory = "build/static-tables";
const binary = path.join(directory, "tables.wasm");
const options = { encoding: "utf8", timeout: 120000 };
fs.mkdirSync(directory, { recursive: true });
runChecked(["lake", "build", "lean-wasm", moduleName], options);
const entries = ["lookup", "provedLookup", "lookupSecond", "lookupEmpty", "changed", "afterChange"];
runChecked([compiler, "compile", "--module", moduleName, "--entries",
  entries.map(name => `${moduleName}.${name}`).join(","), "--out", binary], options);
for (const [entry, words] of [["lookup", [0n, 65n, 1n << 63n, (1n << 64n) - 1n]],
  ["lookupSecond", [7n, 11n]]]) {
  words.forEach((word, index) => {
    const stats = host.callStats(binary, entry, "i64", [host.i64(index)]);
    assert.equal(BigInt(stats.result), word);
    assert.equal(stats.allocs, 0n);
  });
}
for (const [entry, index] of [["lookup", 4n], ["lookup", (1n << 64n) - 1n], ["lookupEmpty", 0n]]) {
  const result = spawnResult([host.ensureHost(), "call", binary, entry, "i64", host.i64(index)], options);
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, /unreachable/);
}
assert.equal(host.callI64(binary, "afterChange", [host.i64(1), host.i64(9)]), 74n);
assert.equal(host.callI64(binary, "provedLookup", [host.i64(5)]), 65n);
const session = ["arg-u64 1", "arg-u64 9", "call changed 1", "arg-u64 result:0", "call release 0",
  "call reset 0", "arg-u64 8192", "call alloc 1", "arg-u64 1", "call lookup 1", "done"].join("\n") + "\n";
const output = runChecked([host.ensureHost(), "session", binary], { ...options, input: session }).stdout;
assert.equal(output.trim().split("\n").at(-1), "results 65");

const single = path.join(directory, "lookup.wasm");
const wat = path.join(directory, "lookup.wat");
for (const [mode, out] of [["compile", single], ["compile-wat", wat]]) {
  runChecked([compiler, mode, "--module", moduleName, "--entry", `${moduleName}.lookup`, "--out", out], options);
}
const parsed = path.join(directory, "lookup-parsed.wasm");
runChecked([process.env.WASM_TOOLS || "wasm-tools", "parse", wat, "-o", parsed], options);
assert.deepEqual(fs.readFileSync(parsed), fs.readFileSync(single));
const image = spawnResult([compiler, "compile-image", "--module", moduleName,
  "--entry", `${moduleName}.lookup`, "--out", path.join(directory, "lookup.image")], options);
assert.notEqual(image.status, 0);
assert.match(image.stderr, /image schema v2 does not support static data/);
const wasi = path.join(directory, "output.wasm");
runChecked([compiler, "compile-wasi", "--module", moduleName, "--entry", `${moduleName}.output`, "--out", wasi], options);
assert.equal(runChecked([process.env.WASMTIME || "build/tools/wasmtime/current/wasmtime", wasi], options).stdout, "A");
process.stdout.write("Passed static table reads, bounds, allocation, copying, reset, WAT, and WASI tests\n");
