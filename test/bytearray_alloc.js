#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.ByteArrayPrograms";
const entryName = `${moduleName}.firstBytePlusArray`;
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const out = path.join(".lake", "build", "bytearray-first-plus-array.wasm");

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args[0]} failed`);
  }
  return result;
}

function writeInput(memory, ptr, input) {
  new Uint8Array(memory.buffer, ptr, input.length).set(input);
}

async function main() {
  run(["lake", "build", moduleName]);
  run([leanExe, "compile", "--module", moduleName, "--entry", entryName, "--out", out]);

  const wasm = fs.readFileSync(out);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const { memory, alloc, reset, firstBytePlusArray } = instance.exports;
  if (!memory || typeof alloc !== "function" || typeof reset !== "function") {
    throw new Error("compiled module does not export memory, alloc, and reset");
  }
  if (typeof firstBytePlusArray !== "function") {
    throw new Error("compiled module does not export firstBytePlusArray");
  }

  const cases = [
    { input: new Uint8Array([]), expected: 5n },
    { input: new Uint8Array([37]), expected: 42n },
    { input: new Uint8Array([255]), expected: 260n },
  ];

  for (const testCase of cases) {
    reset();
    const ptr = Number(alloc(BigInt(testCase.input.length)));
    writeInput(memory, ptr, testCase.input);
    const actual = BigInt.asUintN(64, firstBytePlusArray(BigInt(ptr), BigInt(testCase.input.length)));
    if (actual !== testCase.expected) {
      throw new Error(`expected ${testCase.expected}, got ${actual}`);
    }
  }

  process.stdout.write(`checked ${cases.length} bytearray allocation cases\n`);
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
