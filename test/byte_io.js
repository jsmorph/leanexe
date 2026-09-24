#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked, spawnResult } = require("../tools/run-process");
const { run } = require("./wasi_io_host");

const source = "LeanExe.Examples.ByteIO";
const compiler = process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm";
const wasmTools = process.env.WASM_TOOLS || "wasm-tools";
const outDir = ".lake/build/byte-io";

function compile(name) {
  const wasm = path.join(outDir, `${name}.wasm`);
  runChecked([compiler, "compile-wasi-io", "--module", source,
    "--entry", `${source}.${name}`, "--out", wasm]);
  runChecked([wasmTools, "validate", wasm]);
  return wasm;
}

async function main() {
  fs.mkdirSync(outDir, { recursive: true });
  runChecked(["lake", "build", "lean-wasm", source], { stdio: "inherit" });
  runChecked(["tools/build-wasi-io-host.sh"]);
  const entries = ["echo", "ordered", "timeout", "handled", "reused", "unused",
    "invalid", "immediate", "blocked", "ignored", "emptyWrite", "maxTimeout", "called", "repeated",
    "discardRead", "ignoreReadError", "released", "streaming", "alternatingReads", "streamingTimeout",
    "carried", "chosen", "literalReleased"];
  const programs = Object.fromEntries(entries.map(name => [name, compile(name)]));
  let count = 0;
  async function expect(name, input, status, output, options) {
    let result;
    try { result = await run(programs[name], input, options); }
    catch (error) { throw new Error(`${name}: ${error.message}`, { cause: error }); }
    assert.equal(result.status, status, name);
    if (output !== null) assert.deepEqual(result.output, Buffer.from(output), name);
    count += 1;
  }
  const binary = Buffer.from([0, 255, 13, 10]);
  await expect("echo", binary, 0, binary);
  await expect("echo", Buffer.alloc(0), 0, "");
  await expect("echo", Buffer.from("abcdef"), 0, "abcd");
  await expect("ordered", "", 0, "AB");
  await expect("ignored", "", 0, "AB");
  await expect("reused", "12", 0, "12");
  await expect("unused", "", 0, "ok");
  await expect("invalid", undefined, 28, "");
  await expect("immediate", undefined, 73, "");
  await expect("immediate", binary, 0, binary);
  const start = performance.now();
  await expect("timeout", undefined, 73, "");
  assert.ok(performance.now() - start >= 40, "read timeout fired early");
  await expect("handled", undefined, 0, "timeout");
  await expect("handled", "x", 0, "read");
  await expect("echo", child => {
    const timer = setTimeout(() => child.stdin.end(binary), 100);
    child.once("exit", () => clearTimeout(timer));
  }, 0, binary);
  await expect("blocked", "", 73, null, { drain: false });
  await expect("ordered", child => { child.stdout.destroy(); child.stdin.end(); }, 64, "");
  await expect("emptyWrite", "", 0, "");
  await expect("maxTimeout", binary, 0, binary);
  await expect("called", "", 0, "AB");
  await expect("discardRead", "12", 0, "2");
  await expect("ignoreReadError", "", 0, "ok");
  await expect("released", "x", 0, "");
  await expect("released", "", 0, "");
  await expect("repeated", "", 0, "xxx");
  await expect("streaming", Buffer.alloc(0), 0, "");
  await expect("streaming", binary, 0, binary);
  const stream = Buffer.alloc(4 * 1024 * 1024 + 137);
  for (let i = 0; i < stream.length; i += 1) stream[i] = (i * 73) ^ (i >>> 8) ^ (i >>> 16);
  await expect("streaming", stream, 0, stream);
  await expect("alternatingReads", "ab", 0, "ab");
  const prefix = stream.subarray(0, 4097);
  await expect("streamingTimeout", child => child.stdin.write(prefix), 73, prefix);
  await expect("streamingTimeout", stream, 73, null, { drain: false });
  await expect("streamingTimeout", child => {
    child.stdout.destroy();
    child.stdin.end(prefix);
  }, 64, "");
  await expect("carried", "Iabc", 0, "IabcI");
  await expect("carried", child => child.stdin.write("Ia"), 73, "I");
  await expect("carried", child => {
    child.stdout.destroy();
    child.stdin.end("Iabc");
  }, 64, "");
  await expect("chosen", "", 0, "AC");
  await expect("chosen", "x", 0, "BC");
  await expect("literalReleased", "", 0, "ABCABCABC");
  await expect("literalReleased", child => {
    child.stdout.destroy();
    child.stdin.end();
  }, 64, "");
  await expect("blocked", child => {
    child.stdin.end();
    const timer = setInterval(() => child.stdout.read(4096), 10);
    child.once("exit", () => clearInterval(timer));
  }, 73, null, { drain: false });
  const complete = await run(programs.blocked, "");
  assert.equal(complete.status, 0);
  assert.deepEqual(complete.output, Buffer.alloc(1048576, 65));
  count += 1;
  for (const command of ["compile", "compile-image", "compile-wat", "compile-wasi"]) {
    const result = spawnResult([compiler, command, "--module", source,
      "--entry", `${source}.echo`, "--out", path.join(outDir, "rejected.wasm")]);
    assert.notEqual(result.status, 0, `${command} accepted an effectful entry`);
    assert.match(result.stderr.toString(), /ByteIO|unsupported|program entry/i);
  }
  process.stdout.write(`checked ${count} ByteIO runs and four pure-mode rejections\n`);
}

main().catch(error => { process.stderr.write(`${error.stack}\n`); process.exitCode = 1; });
