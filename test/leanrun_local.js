#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

const repoRoot = path.resolve(__dirname, "..");
const leanrun = path.join(repoRoot, "tools", "leanrun");
const root = makeTemporaryDirectory("leanexe-leanrun-local-");
const toolchain = path.join(root, "toolchain");
const toolchainBin = path.join(toolchain, "bin");
const lockDirectory = path.join(root, "lock");
const cacheDirectory = path.join(root, "cache");
const systemdMarker = path.join(root, "systemd-run-called");

function writeExecutable(file, contents) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, contents);
  fs.chmodSync(file, 0o755);
}

function runLeanrun(args, localMode) {
  const env = {
    ...process.env,
    LEANRUN_LOCAL: localMode,
    LEANRUN_TOOLCHAIN: toolchain,
    LEANRUN_LOCKDIR: lockDirectory,
    LEANRUN_CACHE_HOME: cacheDirectory,
    LEANRUN_TEST_SYSTEMD_MARKER: systemdMarker,
  };
  delete env.LEANRUN_IN_SCOPE;
  return spawnSync(leanrun, args, {
    cwd: repoRoot,
    env,
    encoding: "utf8",
    timeout: 5000,
  });
}

function expectStatus(name, result, expected) {
  if (result.error) {
    throw new Error(`${name}: failed to run leanrun: ${result.error.message}`);
  }
  if (result.status !== expected) {
    throw new Error(
      `${name}: expected status ${expected}, got ${result.status}\nstdout:\n${result.stdout}\nstderr:\n${result.stderr}`,
    );
  }
}

try {
  writeExecutable(path.join(toolchainBin, "lean"), "#!/bin/sh\nexit 0\n");
  writeExecutable(
    path.join(toolchainBin, "systemd-run"),
    "#!/bin/sh\nset -eu\n: > \"$LEANRUN_TEST_SYSTEMD_MARKER\"\nexit 91\n",
  );

  const probe = [
    "const payload = {",
    "  marker: process.argv[1],",
    "  threads: process.env.LEAN_NUM_THREADS,",
    "  noColor: process.env.NO_COLOR,",
    "  cache: process.env.XDG_CACHE_HOME,",
    "};",
    "process.stdout.write(JSON.stringify(payload));",
  ].join("\n");
  const local = runLeanrun([
    "--timeout",
    "2s",
    process.execPath,
    "-e",
    probe,
    "local-command-reached",
  ], "1");
  expectStatus("local invocation", local, 0);
  const payload = JSON.parse(local.stdout);
  if (payload.marker !== "local-command-reached" ||
      payload.threads !== "1" || payload.noColor !== "1" ||
      payload.cache !== cacheDirectory) {
    throw new Error(`local invocation: unexpected child environment ${local.stdout}`);
  }
  if (fs.existsSync(systemdMarker)) {
    throw new Error("local invocation called systemd-run");
  }

  const invalidCommandMarker = path.join(root, "invalid-command-called");
  const invalid = runLeanrun([
    process.execPath,
    "-e",
    `require("node:fs").writeFileSync(${JSON.stringify(invalidCommandMarker)}, "called")`,
  ], "definitely-not-valid");
  expectStatus("invalid LEANRUN_LOCAL", invalid, 2);
  if (!invalid.stderr.includes("LEANRUN_LOCAL")) {
    throw new Error(`invalid LEANRUN_LOCAL: missing diagnostic:\n${invalid.stderr}`);
  }
  if (fs.existsSync(invalidCommandMarker) || fs.existsSync(systemdMarker)) {
    throw new Error("invalid LEANRUN_LOCAL reached a command instead of rejecting the value");
  }

  const standard = runLeanrun([
    "--timeout",
    "2s",
    process.execPath,
    "-e",
    "process.exit(0)",
  ], "0");
  expectStatus("standard invocation", standard, 91);
  if (!fs.existsSync(systemdMarker)) {
    throw new Error("standard invocation did not call systemd-run");
  }
  fs.rmSync(systemdMarker);

  const timed = runLeanrun([
    "--timeout",
    "0.05s",
    process.execPath,
    "-e",
    "setTimeout(() => process.stdout.write('late'), 2000)",
  ], "1");
  expectStatus("local timeout", timed, 124);
  if (timed.stdout !== "") {
    throw new Error(`local timeout: child ran past its deadline: ${JSON.stringify(timed.stdout)}`);
  }
  if (fs.existsSync(systemdMarker)) {
    throw new Error("local timeout called systemd-run");
  }

  const nested = runLeanrun([
    "--timeout",
    "2s",
    leanrun,
    "--lock-timeout",
    "1",
    process.execPath,
    "-e",
    "process.exit(0)",
  ], "1");
  expectStatus("nested local invocation", nested, 1);
  if (!nested.stderr.includes("nested tools/leanrun is not supported") ||
      !nested.stderr.includes("LEANRUN_LOCAL=1") ||
      !nested.stderr.includes("invoke the repository driver directly")) {
    throw new Error(`nested local invocation: missing explanatory diagnostic:\n${nested.stderr}`);
  }
  if (fs.existsSync(systemdMarker)) {
    throw new Error("nested local invocation called systemd-run");
  }
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}

process.stdout.write(
  "checked leanrun opt-in local execution, standard-mode preservation, validation, timeout enforcement, and nesting rejection\n",
);
