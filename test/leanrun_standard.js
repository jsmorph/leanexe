#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

if (process.platform !== "linux") process.exit(0);
const root = makeTemporaryDirectory("leanexe-leanrun-standard-");
const toolchain = path.join(root, "toolchain");
const installedRunner = path.join(root, "leanrun");
const wrapper = path.resolve(__dirname, "../tools/leanrun");
const receipt = path.join(root, "receipt.json");
const limits = {
  LEANRUN_MEMORY_HIGH: "4G", LEANRUN_MEMORY_MAX: "6G", LEANRUN_SWAP_MAX: "1G",
  LEANRUN_CPU_QUOTA: "100%", LEANRUN_TASKS_MAX: "512", LEANRUN_NICE: "10", LEANRUN_JOBS: "1",
};
const env = {
  ...process.env,
  LEANRUN_LOCAL: "0", LEANRUN_RUNNER: installedRunner, LEANRUN_TOOLCHAIN: toolchain,
  LEANRUN_CACHE_HOME: path.join(root, "cache"),
  LEANRUN_MEMORY_MAX: "100G", LEANRUN_CPU_QUOTA: "800%", LEANRUN_JOBS: "8",
};
for (const name of ["LEANRUN_IN_SCOPE", "LEANRUN_LOCAL_IN_SCOPE", "LEANRUN_LOCK_TIMEOUT", "LEANRUN_TIMEOUT"]) {
  delete env[name];
}

function run(args, overrides = {}) {
  const result = spawnSync(wrapper, args, { env: { ...env, ...overrides }, encoding: "utf8", timeout: 5000 });
  if (result.error) throw result.error;
  return result;
}

try {
  fs.mkdirSync(path.join(toolchain, "bin"), { recursive: true });
  fs.writeFileSync(path.join(toolchain, "bin/lean"), "#!/bin/sh\nexit 99\n", { mode: 0o755 });
  fs.writeFileSync(installedRunner, `#!${process.execPath}
const fs = require("node:fs");
fs.writeFileSync(${JSON.stringify(receipt)}, JSON.stringify({args: process.argv.slice(2), env: process.env}));
process.exit(37);
`, { mode: 0o755 });

  for (const [duration, seconds] of [["30s", "30"], ["2m", "120"], ["1h", "3600"], ["1d", "86400"], ["007", "7"]]) {
    const result = run(["--timeout", duration, "lean", "argument with spaces"]);
    assert.equal(result.status, 37, result.stderr);
    const observed = JSON.parse(fs.readFileSync(receipt, "utf8"));
    assert.deepEqual(observed.args, ["env", "LEANRUN_IN_SCOPE=1", "timeout", duration, "lean", "argument with spaces"]);
    for (const [name, value] of Object.entries(limits)) assert.equal(observed.env[name], value, name);
    assert.equal(observed.env.LEANRUN_TIMEOUT, seconds);
    assert.equal(observed.env.LEANRUN_TOOLCHAIN, toolchain);
    assert.equal(observed.env.LEAN_NUM_THREADS, "1");
    assert.equal(observed.env.NO_COLOR, "1");
  }
  assert.equal(run(["lean"]).status, 37);
  assert.equal(JSON.parse(fs.readFileSync(receipt)).env.LEANRUN_TIMEOUT, "900");
  fs.unlinkSync(receipt);
  for (const duration of ["0", "0s", "-1", "1.5s", "bad", "999999999d", "999999999999999999999h"]) {
    const result = run(["--timeout", duration, "lean"]);
    assert.equal(result.status, 2, result.stderr);
    assert.equal(fs.existsSync(receipt), false);
  }
  for (const result of [
    run(["--lock-timeout", "1", "lean"]),
    run(["lean"], { LEANRUN_LOCK_TIMEOUT: "1" }),
    run(["--lock-timeout", "1", "lean"], { LEANRUN_IN_SCOPE: "1" }),
  ]) {
    assert.equal(result.status, 2);
    assert.match(result.stderr, /standard mode waits for the shared slot/);
  }
  const missing = run(["lean"], { LEANRUN_RUNNER: path.join(root, "missing") });
  assert.equal(missing.status, 2);
  assert.match(missing.stderr, /installed runner not found/);
  assert.equal(fs.existsSync(receipt), false);
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}
console.log("checked installed-runner delegation, fixed limits, duration conversion, argument/exit preservation, and rejected options");
