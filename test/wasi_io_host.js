#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { spawn } = require("node:child_process");
const { runChecked } = require("../tools/run-process");

const root = path.resolve(__dirname, "..");
const outDir = path.join(root, ".lake/build/wasi-io-host");
const host = process.env.LEANEXE_WASI_IO_HOST || path.join(root, "build/tools/leanexe-wasi-io-host");
const wasmTools = process.env.WASM_TOOLS || "wasm-tools";

function compile(name, body) {
  const wat = path.join(outDir, `${name}.wat`);
  const wasm = path.join(outDir, `${name}.wasm`);
  fs.writeFileSync(wat, `(module
    (import "wasi_snapshot_preview1" "fd_fdstat_set_flags" (func $flags (param i32 i32) (result i32)))
    (import "wasi_snapshot_preview1" "fd_read" (func $read (param i32 i32 i32 i32) (result i32)))
    (import "wasi_snapshot_preview1" "fd_write" (func $write (param i32 i32 i32 i32) (result i32)))
    (import "wasi_snapshot_preview1" "poll_oneoff" (func $poll (param i32 i32 i32 i32) (result i32)))
    (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))
    (memory (export "memory") 1)
    (func $check (param $error i32)
      (if (local.get $error) (then (call $exit (local.get $error)))))
    (func (export "_start") ${body}))\n`);
  runChecked([wasmTools, "parse", wat, "-o", wasm], { cwd: root });
  return wasm;
}

function run(wasm, input, { drain = true } = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(host, [wasm], { cwd: root, stdio: ["pipe", "pipe", "pipe"] });
    const output = [], errors = [];
    if (drain) child.stdout.on("data", chunk => output.push(chunk));
    child.stderr.on("data", chunk => errors.push(chunk));
    child.stdin.on("error", error => { if (error.code !== "EPIPE") reject(error); });
    const timer = setTimeout(() => { child.kill("SIGKILL"); reject(new Error("WASI host exceeded 5s watchdog")); }, 5000);
    child.on("error", error => { clearTimeout(timer); reject(error); });
    child.on("exit", (status, signal) => {
      clearTimeout(timer);
      if (!drain) child.stdout.resume();
      child.once("close", () => {
        child.stdin.destroy();
        const stderr = Buffer.concat(errors).toString();
        if (signal || stderr) reject(new Error(`WASI host: ${signal || stderr}`));
        else resolve({ status, output: Buffer.concat(output) });
      });
    });
    if (typeof input === "function") input(child);
    else if (input !== undefined) child.stdin.end(input);
  });
}

async function main() {
  fs.mkdirSync(outDir, { recursive: true });
  runChecked([path.join(root, "tools/build-wasi-io-host.sh")], { cwd: root });
  const nonblocking = compile("nonblocking", `
    (call $check (call $flags (i32.const 0) (i32.const 4)))
    (i32.store (i32.const 0) (i32.const 1024))
    (i32.store (i32.const 4) (i32.const 4))
    (call $exit (call $read (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 8)))`);
  assert.equal((await run(nonblocking)).status, 6);
  assert.equal((await run(nonblocking, Buffer.alloc(0))).status, 0);
  const fault = compile("fault", `(call $exit (call $read (i32.const 0) (i32.const 65532) (i32.const 1) (i32.const 8)))`);
  assert.equal((await run(fault, Buffer.from("x"))).status, 21);

  const pollRead = compile("poll-read", `
    (call $check (call $flags (i32.const 0) (i32.const 4)))
    (call $check (call $flags (i32.const 1) (i32.const 4)))
    (i32.store (i32.const 80) (i32.const 1))
    (i64.store (i32.const 88) (i64.const 50000000))
    (i32.store8 (i32.const 120) (i32.const 1))
    (call $check (call $poll (i32.const 64) (i32.const 160) (i32.const 2) (i32.const 224)))
    (if (i32.eqz (i32.or
      (i32.eq (i32.load8_u (i32.const 170)) (i32.const 1))
      (i32.and (i32.eq (i32.load (i32.const 224)) (i32.const 2))
        (i32.eq (i32.load8_u (i32.const 202)) (i32.const 1)))))
      (then (call $exit (i32.const 73))))
    (i32.store (i32.const 0) (i32.const 1024))
    (i32.store (i32.const 4) (i32.const 4))
    (call $check (call $read (i32.const 0) (i32.const 0) (i32.const 1) (i32.const 8)))
    (i32.store (i32.const 4) (i32.load (i32.const 8)))
    (call $check (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8)))`);
  let started = performance.now();
  assert.equal((await run(pollRead)).status, 73);
  assert.ok(performance.now() - started >= 40, "clock subscription returned too early");
  const binary = Buffer.from([0, 255, 13, 10]);
  const echoed = await run(pollRead, binary);
  assert.equal(echoed.status, 0);
  assert.deepEqual(echoed.output, binary);
  const eof = await run(pollRead, Buffer.alloc(0));
  assert.equal(eof.status, 0);
  assert.equal(eof.output.length, 0);

  const blockedOutput = compile("blocked-output", `
    (call $check (call $flags (i32.const 1) (i32.const 4)))
    (i32.store (i32.const 0) (i32.const 1024))
    (i32.store (i32.const 4) (i32.const 32768))
    (loop $fill
      (call $check (call $write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8)))
      (br $fill))`);
  assert.equal((await run(blockedOutput, Buffer.alloc(0), { drain: false })).status, 6);
  const flagsHarness = path.join(outDir, "flags-harness");
  runChecked(["cc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
    path.join(root, "test/fixtures/wasi-io-flags.c"), "-o", flagsHarness], { cwd: root });
  let flagsCases = 0;
  for (const [name, descriptors, exit] of [
    ["read-first", [0, 1], 0], ["write-first", [1, 0], 0],
    ["read-only", [0], 0], ["write-only", [1], 0],
    ["repeated", [0, 1, 0, 1], 0], ["error-exit", [0, 1], 7],
  ]) {
    const wasm = compile(`flags-${name}`, descriptors.map(fd =>
      `(call $check (call $flags (i32.const ${fd}) (i32.const 4)))`).join("\n") +
      `\n(call $exit (i32.const ${exit}))`);
    for (const nonblocking of [0, 1]) {
      runChecked([flagsHarness, host, wasm, String(nonblocking), String(exit)],
        { cwd: root, timeout: 10000 });
      flagsCases += 1;
    }
  }
  process.stdout.write(`checked 7 WASI I/O host cases and ${flagsCases} shared-descriptor restorations\n`);
}

module.exports = { run };

if (require.main === module) {
  main().catch(error => { process.stderr.write(`${error.stack}\n`); process.exitCode = 1; });
}
