#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked, spawnResult } = require("../tools/run-process");

const source = "LeanExe.Examples.Wasi";
const compiler = process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm";
const wasmTools = process.env.WASM_TOOLS || "wasm-tools";
const wasmtime = process.env.WASMTIME || "build/tools/wasmtime/current/wasmtime";
const outDir = ".lake/build/wasi-api";
const programs = new Map();
let count = 0;

function compile(name) {
  if (programs.has(name)) return programs.get(name);
  const wasm = path.join(outDir, `${name}.wasm`);
  runChecked([compiler, "compile-wasi-api", "--module", source,
    "--entry", `${source}.${name}`, "--out", wasm]);
  runChecked([wasmTools, "validate", wasm]);
  programs.set(name, wasm);
  return wasm;
}

function expect(name, input, status, output, options = [], args = []) {
  const result = spawnResult([wasmtime, "run", ...options, compile(name), ...args],
    { input, timeout: 10000, maxBuffer: 16 * 1024 * 1024 });
  assert.equal(result.status, status, `${name}: ${result.stderr}`);
  assert.equal(result.signal, null, name);
  if (output !== null) assert.deepEqual(result.stdout, Buffer.from(output), name);
  count += 1;
  return result.stdout;
}

fs.mkdirSync(outDir, { recursive: true });
runChecked(["lake", "build", "lean-wasm", source], { stdio: "inherit" });
const binary = Buffer.from([0, 255, 13, 10]);
expect("echo", binary, 0, binary);
expect("echo", "", 0, "");
expect("ordered", "", 0, "ABA");
expect("clock", "", 0, "");
expect("arguments", "", 0, "test\0alpha\0\0β\0", ["--argv0", "test"], ["alpha", "", "β"]);
expect("environment", "", 0, "WASI_TEST=value\0", ["--env", "WASI_TEST=value"]);
expect("environment", "", 0, "");
const a = expect("random", "", 0, null);
const b = expect("random", "", 0, null);
assert.equal(a.length, 64);
assert.notDeepEqual(a, b);
expect("timer", "", 0, "");
expect("ready", "input", 0, "");
expect("invalidPoll", "", 28, "");
expect("exit", "", 17, "");
expect("errors", "", 0, "");
const fixture = path.resolve(outDir, "files");
fs.rmSync(fixture, { recursive: true, force: true });
fs.mkdirSync(fixture);
expect("filesystem", "", 0, "", ["--dir", `${fixture}::test`]);
assert.deepEqual(fs.readdirSync(fixture), []);
expect("renumber", "", 0, "", ["--dir", `${fixture}::test`]);
assert.equal(fs.readFileSync(path.join(fixture, "file"), "utf8"), "renumbered");
expect("empty", "x", 0, "");
expect("released", "", 0, "", ["--env", "OWNERSHIP=value"]);
expect("socketErrors", "", 0, "");
for (const command of ["compile", "compile-wat", "compile-image", "eval-ir"]) {
  const args = [compiler, command, "--module", source, "--entry", `${source}.echo`];
  if (command !== "eval-ir") args.push("--out", path.join(outDir, "rejected"));
  const result = spawnResult(args, { encoding: "utf8" });
  assert.notEqual(result.status, 0, command);
  assert.match(result.stderr + result.stdout, /require compile-wasi-api/);
  count += 1;
}
console.log(`${count} WASI API tests passed`);
