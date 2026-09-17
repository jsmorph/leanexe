"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { spawn } = require("node:child_process");
const { createInterface } = require("node:readline");
const { once } = require("node:events");
const { performance } = require("node:perf_hooks");
const { parentPort, workerData } = require("node:worker_threads");
const root = path.resolve(__dirname, "../..");
const control = new Int32Array(workerData.control);
const response = new Uint8Array(workerData.response);
let log, child, pending, failure, nativeStartupMs;

function reply(value) {
  let bytes = Buffer.from(JSON.stringify(value));
  if (bytes.length > response.length) bytes = Buffer.from('{"error":"native response exceeds bounded capacity"}');
  response.set(bytes);
  Atomics.store(control, 1, bytes.length);
  Atomics.store(control, 0, 1);
  Atomics.notify(control, 0);
}

function send(value) {
  if (failure) return Promise.reject(failure);
  if (pending) return Promise.reject(new Error("concurrent native requests are forbidden"));
  return new Promise((resolve, reject) => {
    pending = { resolve, reject };
    child.stdin.write(JSON.stringify(value) + "\n");
  });
}

async function start() {
  const startedAt = performance.now();
  log = fs.openSync(workerData.log, "wx");
  const command = process.platform === "darwin" ? path.join(__dirname, "run-macos-cpu.sh") :
    (process.env.LEANEXE_WGPU_PYTHON || "python3");
  const args = process.platform === "darwin" ? ["--session"] : [path.join(__dirname, "run.py"), "--session"];
  child = spawn(command, args, { cwd: root, env: process.env, stdio: ["pipe", "pipe", "pipe"] });
  const fail = error => { failure = error; pending?.reject(error); pending = undefined; };
  child.on("error", fail);
  child.stdin.on("error", fail);
  child.stderr.on("data", bytes => fs.writeSync(log, bytes));
  createInterface({ input: child.stdout }).on("line", line => {
    fs.writeSync(log, line + "\n");
    try {
      if (!pending) throw new Error("unsolicited native response");
      const value = JSON.parse(line);
      const current = pending;
      pending = undefined;
      current.resolve(value);
    } catch (error) { fail(error); }
  });
  child.on("exit", (code, signal) => {
    if (pending) fail(new Error(`native session exited during request (${code}, ${signal})`));
  });
  const ready = await send(workerData.job);
  if (!ready.ready || ready.error) throw new Error(ready.error || "native session did not become ready");
  nativeStartupMs = performance.now() - startedAt;
}

const started = start();
// Keep setup rejection handled until the first synchronous caller requests it.
started.catch(() => {});
parentPort.on("message", async message => {
  try {
    await started;
    if (message.type === "close") {
      if (child.exitCode !== null || child.signalCode !== null)
        throw new Error(`native session exited before orderly close (${child.exitCode}, ${child.signalCode})`);
      const exited = once(child, "close");
      child.stdin.end();
      const [code] = await exited;
      if (code !== 0) throw new Error(`native session closed with exit ${code}`);
      fs.closeSync(log);
      reply({ closed: true });
    } else {
      const value = await send({ a: message.a });
      if (value.resident) value.resident.nativeStartupMs = nativeStartupMs;
      reply(value);
    }
  } catch (error) {
    child?.kill();
    reply({ error: error.message });
  }
});
