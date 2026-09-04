"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("./run-process");

const repoRoot = path.resolve(__dirname, "..");
const defaultHostExecutable = path.join(repoRoot, "build", "tools", "leanexe-wasmtime-host");
const buildHostScript = path.join(repoRoot, "tools", "build-wasmtime-host.sh");
const maxUInt64 = (1n << 64n) - 1n;

function configuredHostExecutable() {
  if (process.env.LEANEXE_WASMTIME_HOST) {
    return path.resolve(process.env.LEANEXE_WASMTIME_HOST);
  }
  return defaultHostExecutable;
}

function ensureHost() {
  const executable = configuredHostExecutable();
  if (!fs.existsSync(executable)) {
    runChecked([buildHostScript], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LEANEXE_WASMTIME_HOST: executable },
    });
  }
  if (!fs.existsSync(executable)) {
    throw new Error(`Wasmtime host runner was not built: ${executable}`);
  }
  return executable;
}

function i64Argument(value) {
  return `i64:${BigInt.asUintN(64, BigInt(value)).toString(10)}`;
}

function parseI64SlotsOutput(exportName, resultCount, output) {
  const fields = output.trim().split(/\s+/).filter(Boolean);
  if (fields.length !== resultCount || fields.some((field) => !/^[0-9]+$/.test(field))) {
    throw new Error(
      `${exportName}: Wasmtime host returned ${JSON.stringify(output.trim())}; ` +
      `expected ${resultCount} unsigned i64 words`,
    );
  }
  return fields.map((field) => {
    const value = BigInt(field);
    if (value > maxUInt64) {
      throw new Error(
        `${exportName}: Wasmtime host returned an integer outside UInt64: ${field}`,
      );
    }
    return value;
  });
}

function callI64Slots(wasmPath, exportName, resultCount, arguments_) {
  if (!Number.isSafeInteger(resultCount) || resultCount < 0 || resultCount > 128) {
    throw new Error(`invalid Wasmtime result-slot count: ${resultCount}`);
  }
  const executable = ensureHost();
  const result = runChecked([
    executable,
    "call",
    wasmPath,
    exportName,
    `slots:${resultCount}`,
    ...arguments_.map(i64Argument),
  ], { cwd: repoRoot, encoding: "utf8" });
  return parseI64SlotsOutput(exportName, resultCount, result.stdout);
}

module.exports = {
  callI64Slots,
  ensureHost,
  i64Argument,
  maxUInt64,
  parseI64SlotsOutput,
};
