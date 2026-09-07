#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { spawn } = require("node:child_process");
const { setTimeout: delay } = require("node:timers/promises");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

async function main() {
  if (process.platform !== "darwin") return;
  const root = makeTemporaryDirectory("leanexe-macos-lock-");
  const runner = path.resolve(__dirname, "../tools/leanrun");
  const env = { ...process.env, LEANRUN_LOCAL: "1", LEANRUN_LOCKDIR: path.join(root, "lock") };
  delete env.LEANRUN_LOCAL_IN_SCOPE;
  delete env.LEANRUN_IN_SCOPE;
  function start(code, timeout = "3s", lock = "1") {
    const child = spawn(runner, ["--timeout", timeout, "--lock-timeout", lock,
      process.execPath, "-e", code], { env, stdio: ["ignore", "pipe", "pipe"] });
    let stderr = "";
    child.stderr.on("data", b => { stderr += b; });
    child.stdout.resume();
    const done = new Promise((resolve, reject) => {
      child.once("error", reject);
      child.once("close", (status, signal) => resolve({ status, signal, stderr }));
    });
    return { child, done };
  }
  async function waitFile(file) {
    for (let i = 0; i < 300; ++i) {
      if (fs.existsSync(file)) return;
      await delay(10);
    }
    throw new Error(`runner did not create ${file}`);
  }
  try {
    const entered = path.join(root, "entered");
    const holder = start(`require('node:fs').writeFileSync(${JSON.stringify(entered)}, 'yes'); setTimeout(() => {}, 700)`);
    await waitFile(entered);
    const denied = await start("process.exit(99)", "1s", "0").done;
    assert.equal(denied.status, 75, denied.stderr);
    const waited = start("process.exit(37)", "1s", "2");
    assert.equal((await holder.done).status, 0);
    assert.equal((await waited.done).status, 37);

    const late = path.join(root, "descendant-ran-late");
    const descendant = `process.on('SIGTERM', () => {}); setTimeout(() => require('node:fs').writeFileSync(${JSON.stringify(late)}, 'late'), 900)`;
    const timed = start(`require('node:child_process').spawn(process.execPath, ['-e', ${JSON.stringify(descendant)}], {stdio:'inherit'}); setTimeout(() => {}, 5000)`, "0.2s");
    assert.equal((await timed.done).status, 124);
    await delay(1000);
    assert.equal(fs.existsSync(late), false, "timeout left a live descendant");

    const signaledMarker = path.join(root, "signaled-started");
    const signaled = start(`require('node:fs').writeFileSync(${JSON.stringify(signaledMarker)}, 'yes'); setTimeout(() => {}, 5000)`);
    await waitFile(signaledMarker);
    signaled.child.kill("SIGTERM");
    assert.equal((await signaled.done).status, 143);
    assert.equal((await start("process.exit(0)", "1s", "0").done).status, 0);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
  console.log("checked Darwin lock exclusion, waiting, exit codes, descendant timeout, signal forwarding, and lock release");
}
main().catch(error => { console.error(error); process.exitCode = 1; });
