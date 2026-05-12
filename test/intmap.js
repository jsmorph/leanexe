#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.IntMap";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const outDir = path.join(".lake", "build", "intmap-programs");

function run(args) {
  const result = spawnSync(args[0], args.slice(1), {
    encoding: "utf8",
    env: { ...process.env, XDG_CACHE_HOME: path.join(process.cwd(), ".lake", "build", "cache") },
  });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args[0]} failed`);
  }
  return result.stdout.trim();
}

function compile(entry) {
  const out = path.join(outDir, `${entry}.wasm`);
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
  return out;
}

function invoke(wasm, entry, args = []) {
  const output = run([wasmtime, "--invoke", entry, wasm, ...args.map((arg) => arg.toString())]);
  return BigInt(output);
}

function expect(name, actual, expected) {
  if (actual !== expected) {
    throw new Error(`${name}: expected ${expected}, got ${actual}`);
  }
}

function main() {
  if (!fs.existsSync(wasmtime)) {
    throw new Error(`wasmtime not found: ${wasmtime}`);
  }
  run(["lake", "build", moduleName]);
  fs.mkdirSync(outDir, { recursive: true });

  const checksum = compile("checksum");
  const query = compile("query");

  expect("checksum", invoke(checksum, "checksum"), 51200n);
  expect("query 1", invoke(query, "query", [1n]), 17n);
  expect("query 100", invoke(query, "query", [100n]), 1007n);
  expect("query 101", invoke(query, "query", [101n]), 0n);

  process.stdout.write("checked 4 intmap cases\n");
}

main();
