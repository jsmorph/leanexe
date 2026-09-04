#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

const repoRoot = path.resolve(__dirname, "..");
const checker = path.join(repoRoot, "tools", "check-wasm-tools-version.sh");
const root = makeTemporaryDirectory("leanexe-wasm-tools-version-");

function fakeWasmTools(name, versionOutput) {
  const executable = path.join(root, name);
  fs.writeFileSync(
    executable,
    `#!/bin/sh\nprintf '%s\\n' ${JSON.stringify(versionOutput)}\n`,
  );
  fs.chmodSync(executable, 0o755);
  return executable;
}

function runChecker(executable) {
  return spawnSync(checker, [], {
    cwd: repoRoot,
    env: { ...process.env, WASM_TOOLS: executable },
    encoding: "utf8",
    timeout: 5000,
  });
}

function expectStatus(name, result, expected) {
  if (result.error) {
    throw new Error(`${name}: failed to run version checker: ${result.error.message}`);
  }
  if (result.status !== expected) {
    throw new Error(
      `${name}: expected status ${expected}, got ${result.status}\nstdout:\n${result.stdout}\nstderr:\n${result.stderr}`,
    );
  }
}

try {
  const exact = runChecker(fakeWasmTools("exact", "wasm-tools 1.251.0"));
  expectStatus("exact release version", exact, 0);
  if (exact.stdout !== "checked wasm-tools 1.251.0\n") {
    throw new Error(`exact release version: unexpected output ${JSON.stringify(exact.stdout)}`);
  }

  const official = runChecker(fakeWasmTools(
    "official",
    "wasm-tools 1.251.0 (a1a178a02 2026-05-28)",
  ));
  expectStatus("official release metadata", official, 0);

  const wrong = runChecker(fakeWasmTools("wrong", "wasm-tools 1.250.0"));
  expectStatus("wrong version", wrong, 1);
  if (!wrong.stderr.includes("expected 1.251.0") ||
      !wrong.stderr.includes("got wasm-tools 1.250.0")) {
    throw new Error(`wrong version: missing mismatch diagnostic:\n${wrong.stderr}`);
  }

  const malformed = runChecker(fakeWasmTools(
    "malformed",
    "wasm-tools 1.251.0 (a1a178a02 2026-05-28) trailing-data",
  ));
  expectStatus("malformed release metadata", malformed, 1);
  if (!malformed.stderr.includes("version mismatch")) {
    throw new Error(`malformed release metadata: missing mismatch diagnostic:\n${malformed.stderr}`);
  }
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}

process.stdout.write(
  "checked wasm-tools exact and official release versions plus wrong and malformed rejection\n",
);
