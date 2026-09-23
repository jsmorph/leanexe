#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const net = require("node:net");
const { spawn } = require("node:child_process");
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
    "--entry", `${source}.${name}`, "--out", wasm], { timeout: 120000 });
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

async function socketTest() {
  const wasm = compile("socket");
  const reserve = net.createServer();
  await new Promise((resolve, reject) => {
    reserve.once("error", reject);
    reserve.listen(0, "127.0.0.1", resolve);
  });
  const port = reserve.address().port;
  await new Promise(resolve => reserve.close(resolve));
  const child = spawn(wasmtime, ["run", "-S", "preview2=n", "-S",
    `tcplisten=127.0.0.1:${port}`, wasm], { stdio: ["ignore", "pipe", "pipe"] });
  const payload = Buffer.from([0, 255, 13, 10]);
  const chunks = [];
  let stderr = "";
  let socket;
  let done;
  let failed;
  let socketError;
  const received = new Promise((resolve, reject) => { done = resolve; failed = reject; });
  const timer = setTimeout(() => {
    socket?.destroy();
    child.kill("SIGKILL");
    failed(new Error("socket test timed out"));
  }, 10000);
  child.stderr.on("data", chunk => {
    stderr += chunk;
    if (!socket && stderr.includes("ready\n")) {
      socket = net.connect(port, "127.0.0.1", () => socket.end(payload));
      socket.on("data", chunk => chunks.push(chunk));
      socket.once("end", done);
      socket.once("error", error => { socketError = error; done(); });
    }
  });
  const exited = new Promise((resolve, reject) => {
    child.once("error", reject);
    child.once("close", status => {
      if (status === 0) resolve();
      else reject(new Error(`socket: status ${status}: ${stderr}`));
    });
  });
  await Promise.all([received, exited]).finally(() => {
    clearTimeout(timer);
    socket?.destroy();
    if (child.exitCode === null) child.kill();
  });
  if (socketError) throw socketError;
  assert.deepEqual(Buffer.concat(chunks), payload);
  count += 1;
}

async function main() {
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
  expect("absoluteTimer", "", 0, "");
  expect("ready", "input", 0, "");
  expect("invalidPoll", "", 28, "");
  expect("exit", "", 17, "");
  expect("errors", "", 0, "");
  const fixture = fs.mkdtempSync(path.resolve(outDir, "files-"));
  expect("filesystem", "", 0, "", ["--dir", `${fixture}::test`]);
  assert.deepEqual(fs.readdirSync(fixture), []);
  expect("renumber", "", 0, "", ["--dir", `${fixture}::test`]);
  assert.equal(fs.readFileSync(path.join(fixture, "file"), "utf8"), "renumbered");
  fs.rmSync(fixture, { recursive: true });
  expect("empty", "x", 0, "");
  expect("zeroRead", "x", 27, "");
  expect("zeroRead", "x", 0, "", ["-S", "preview2=n"]);
  expect("released", "", 0, "", ["--env", "OWNERSHIP=value"]);
  expect("socketErrors", "", 0, "");
  expect("signal", "", 58, "");
  expect("pollBadFd", "", 8, "");
  expect("pollBadFd", "", 8, "", ["-S", "preview2=n"]);
  expect("invalidPollTag", "", 0, "");
  expect("retained", binary, 0, Buffer.concat([Buffer.from("keep"), binary, Buffer.from("keep")]),
    ["--argv0", "keep"]);
  expect("localRetained", "", 0, "keep");
  expect("retainedPair", "", 0, "keepkeep", ["--argv0", "keep"]);
  expect("retainedPair", "", 0, "keeptail", ["--argv0", "keep"], ["tail"]);
  expect("retainedReleased", "", 0, "", ["--argv0", "keep"], ["tail"]);
  const stream = Buffer.alloc(4 * 1024 * 1024 + 137);
  for (let i = 0; i < stream.length; i += 1) stream[i] = (i * 73) ^ (i >>> 8) ^ (i >>> 16);
  expect("streaming", stream, 0, stream);
  expect("streaming", "", 0, "");
  for (const command of ["compile", "compile-wat", "compile-image", "eval-ir"]) {
    const args = [compiler, command, "--module", source, "--entry", `${source}.echo`];
    if (command !== "eval-ir") args.push("--out", path.join(outDir, "rejected"));
    const result = spawnResult(args, { encoding: "utf8" });
    assert.notEqual(result.status, 0, command);
    assert.match(result.stderr + result.stdout, /require compile-wasi-api/);
    count += 1;
  }
  await socketTest();
  console.log(`${count} WASI API tests passed`);
}

main().catch(error => { console.error(error); process.exitCode = 1; });
