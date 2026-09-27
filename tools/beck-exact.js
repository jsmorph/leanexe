#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("./run-process");
const { ensureHost } = require("./wasmtime-host");
const { root, encode, check } = require("./beck");

const wasm = path.join(root, "build/beck-exact/beck.wasm");
const moduleName = "LeanExe.Examples.BeckExact";

function prepare() {
  runChecked(["lake", "build", "lean-wasm", moduleName], { cwd: root, encoding: "utf8", timeout: 900000 });
  fs.mkdirSync(path.dirname(wasm), { recursive: true });
  runChecked([path.join(root, ".lake/build/bin/lean-wasm"), "compile", "--module", moduleName,
    "--entry", `${moduleName}.compute`, "--out", wasm], { cwd: root, encoding: "utf8", timeout: 120000 });
  ensureHost();
}

function execute(words) {
  return JSON.parse(runChecked([ensureHost(), "call", wasm, "compute", "array-u64", `array-u64:${words.join(",")}`],
    { cwd: root, encoding: "utf8", timeout: 60000 }).stdout);
}

if (require.main === module) {
  try {
    if (process.argv.length !== 3) throw new Error("usage: tools/beck-exact.js INPUT.json");
    const input = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
    const words = encode(input);
    prepare();
    const result = check(input, execute(words));
    process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
    if (result.status !== "ok") process.exitCode = 1;
  } catch (error) {
    process.stderr.write(`beck-exact: ${error.message}\n`);
    process.exitCode = 1;
  }
}

module.exports = { root, wasm, prepare, execute, encode, check };
