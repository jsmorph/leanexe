#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.Correctness";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const outDir = path.join(".lake", "build", "wasi-programs");

function run(args) {
  const result = spawnSync(args[0], args.slice(1));
  if (result.status === null && result.error) {
    throw result.error;
  }
  return result;
}

function outputText(result) {
  return Buffer.concat([result.stdout || Buffer.alloc(0), result.stderr || Buffer.alloc(0)]).toString("utf8");
}

function compile(entry) {
  const out = path.join(outDir, `${entry}.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi",
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed to compile`);
  }
  return out;
}

function expectProgram(entry, expectedBytes) {
  const wasm = compile(entry);
  const result = run([wasmtime, "run", wasm]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed in Wasmtime`);
  }
  const expected = Buffer.from(expectedBytes);
  const actual = result.stdout || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`${entry}: expected ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
}

function expectReject(entry, message) {
  const out = path.join(outDir, `${entry}.reject.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi",
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status === 0) {
    throw new Error(`${entry} compiled but should have failed`);
  }
  if (!outputText(result).includes(message)) {
    throw new Error(`${entry}: expected rejection containing "${message}"`);
  }
}

function main() {
  if (!fs.existsSync(wasmtime)) {
    throw new Error(`wasmtime not found: ${wasmtime}`);
  }
  fs.mkdirSync(outDir, { recursive: true });

  expectProgram("byteArrayStringConstReturn", [88, 89, 90]);
  expectProgram("byteArrayAppendReturn", [65, 66, 67]);
  expectProgram("byteArrayFoldByteArrayAccumulator", [1, 2]);
  expectProgram("idRunRangeForByteArrayOutput", [1, 1]);

  expectReject("byteArrayPushSize", "program entry must return ByteArray");
  expectReject("byteArrayBranchHelperReturn", "program entry must take no parameters");

  process.stdout.write("checked 4 WASI program cases and 2 rejections\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
