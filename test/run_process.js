#!/usr/bin/env node

const fs = require("node:fs");
const path = require("path");
const {
  guardedInvocation,
  runChecked,
  runCheckedAsync,
} = require("../tools/run-process");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

function expectFailure(args, expected) {
  try {
    runChecked(args, { encoding: "utf8" });
  } catch (error) {
    for (const text of expected) {
      if (!error.message.includes(text)) {
        throw new Error(`missing ${JSON.stringify(text)} in ${JSON.stringify(error.message)}`);
      }
    }
    return;
  }
  throw new Error(`${args[0]} succeeded but should have failed`);
}

function wait(milliseconds) {
  return new Promise((resolve) => setTimeout(resolve, milliseconds));
}

async function checkAsyncOutput() {
  const result = await runCheckedAsync([
    process.execPath,
    "-e",
    "process.stdout.write('captured output\\n')",
  ]);
  if (result.stdout.toString("utf8") !== "captured output\n") {
    throw new Error("async process output was not captured");
  }
  try {
    await runCheckedAsync([
      process.execPath,
      "-e",
      "process.stderr.write('async failure\\n'); process.exit(9)",
    ]);
  } catch (error) {
    if (!error.message.includes("exited with status 9") ||
        !error.message.includes("async failure")) {
      throw error;
    }
    return;
  }
  throw new Error("async failing process succeeded");
}

async function checkSignalForwarding() {
  const temporaryRoot = makeTemporaryDirectory("leanexe-process-");
  const readyPath = path.join(temporaryRoot, "ready");
  const signalPath = path.join(temporaryRoot, "signal");
  const grandchild = [
    "const fs = require('node:fs');",
    `const signalPath = ${JSON.stringify(signalPath)};`,
    "process.on('SIGTERM', () => { fs.writeFileSync(signalPath, 'SIGTERM'); process.exit(0); });",
    "if (process.send) process.send('ready');",
    "setInterval(() => {}, 1000);",
  ].join("\n");
  const child = [
    "const fs = require('node:fs');",
    "const { spawn } = require('node:child_process');",
    `const readyPath = ${JSON.stringify(readyPath)};`,
    `const grandchild = ${JSON.stringify(grandchild)};`,
    "const nested = spawn(process.execPath, ['-e', grandchild], { stdio: ['ignore', 'ignore', 'ignore', 'ipc'] });",
    "nested.on('message', () => fs.writeFileSync(readyPath, 'ready'));",
    "process.on('SIGTERM', () => process.exit(0));",
    "setInterval(() => {}, 1000);",
  ].join("\n");
  try {
    const running = runCheckedAsync([process.execPath, "-e", child], { stdio: "ignore" });
    for (let attempt = 0; attempt < 100 && !fs.existsSync(readyPath); attempt += 1) {
      await wait(10);
    }
    if (!fs.existsSync(readyPath)) throw new Error("signal test grandchild did not start");
    process.kill(process.pid, "SIGTERM");
    try {
      await running;
      throw new Error("signal-forwarded child succeeded");
    } catch (error) {
      if (!error.message.includes("terminated by SIGTERM")) throw error;
    }
    for (let attempt = 0; attempt < 100 && !fs.existsSync(signalPath); attempt += 1) {
      await wait(10);
    }
    if (fs.readFileSync(signalPath, "utf8") !== "SIGTERM") {
      throw new Error("SIGTERM did not reach the grandchild process");
    }
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true, force: true });
  }
}

async function main() {
  expectFailure(["leanexe-command-that-does-not-exist"], [
    "leanexe-command-that-does-not-exist",
    "failed to start",
    "ENOENT",
  ]);
  expectFailure([
    process.execPath,
    "-e",
    "process.stderr.write('specific failure\\n'); process.exit(7)",
  ], ["exited with status 7", "specific failure"]);
  runChecked([process.execPath, "-e", "process.exit(0)"], { stdio: "ignore" });

  const guarded = guardedInvocation(
    ["lake", "build", "LeanExe"],
    { env: { TEST_MARKER: "present" }, timeout: 1501 },
  );
  if (path.basename(guarded.args[0]) !== "leanrun") {
    throw new Error("lake command did not use leanrun");
  }
  if (guarded.args.slice(1).join("\0") !== ["lake", "build", "LeanExe"].join("\0")) {
    throw new Error("leanrun changed the guarded command");
  }
  if (guarded.options.timeout !== undefined || guarded.options.env.LEANRUN_TIMEOUT !== "2s") {
    throw new Error("leanrun did not receive the process timeout");
  }
  if (guarded.options.env.TEST_MARKER !== "present") {
    throw new Error("leanrun discarded the child environment");
  }

  const unguarded = guardedInvocation([process.execPath, "--version"], { timeout: 1000 });
  if (unguarded.args[0] !== process.execPath || unguarded.options.timeout !== 1000) {
    throw new Error("non-Lean command changed by Lean guard");
  }

  await checkAsyncOutput();
  await checkSignalForwarding();
  process.stdout.write("checked sync and async process errors, output capture, Lean command routing, and signal forwarding\n");
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exitCode = 1;
});
