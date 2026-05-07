#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.ByteArrayPrograms";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "bytearray-programs");

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

function compile(entry, out) {
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
}

async function instantiate(entry) {
  const out = path.join(outDir, `${entry}.wasm`);
  compile(entry, out);
  const wasm = fs.readFileSync(out);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const fn = instance.exports[entry];
  if (typeof fn !== "function") {
    throw new Error(`compiled module does not export ${entry}`);
  }
  const { memory, alloc, reset } = instance.exports;
  if (!memory || typeof alloc !== "function" || typeof reset !== "function") {
    throw new Error("compiled module does not export memory, alloc, and reset");
  }
  return { memory, alloc, reset, fn };
}

function callByteArray(exports, input, args = []) {
  exports.reset();
  const ptr = Number(exports.alloc(BigInt(input.length)));
  writeInput(exports.memory, ptr, input);
  return BigInt.asUintN(64, exports.fn(BigInt(ptr), BigInt(input.length), ...args));
}

async function main() {
  run(["lake", "build", moduleName]);
  fs.mkdirSync(outDir, { recursive: true });

  const firstBytePlusArray = await instantiate("firstBytePlusArray");
  const firstBytePlusArrayCases = [
    { input: new Uint8Array([]), expected: 5n },
    { input: new Uint8Array([37]), expected: 42n },
    { input: new Uint8Array([255]), expected: 260n },
  ];

  for (const testCase of firstBytePlusArrayCases) {
    const actual = callByteArray(firstBytePlusArray, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstBytePlusArray: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteIsStar = await instantiate("firstByteIsStar");
  const firstByteIsStarCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([42]), expected: 1n },
    { input: new Uint8Array([41]), expected: 0n },
  ];

  for (const testCase of firstByteIsStarCases) {
    const actual = callByteArray(firstByteIsStar, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteIsStar: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteNextIsZero = await instantiate("firstByteNextIsZero");
  const firstByteNextIsZeroCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([255]), expected: 1n },
    { input: new Uint8Array([254]), expected: 0n },
  ];

  for (const testCase of firstByteNextIsZeroCases) {
    const actual = callByteArray(firstByteNextIsZero, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteNextIsZero: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteLowNibble = await instantiate("firstByteLowNibble");
  const firstByteLowNibbleCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([0xab]), expected: 11n },
    { input: new Uint8Array([0xf0]), expected: 0n },
  ];

  for (const testCase of firstByteLowNibbleCases) {
    const actual = callByteArray(firstByteLowNibble, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteLowNibble: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteBangIndex = await instantiate("firstByteBangIndex");
  const firstByteBangIndexCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([37]), expected: 37n },
    { input: new Uint8Array([255]), expected: 255n },
  ];

  for (const testCase of firstByteBangIndexCases) {
    const actual = callByteArray(firstByteBangIndex, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteBangIndex: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const byteAtOrZero = await instantiate("byteAtOrZero");
  const byteAtOrZeroCases = [
    { input: new Uint8Array([10, 20, 30]), args: [0n], expected: 10n },
    { input: new Uint8Array([10, 20, 30]), args: [2n], expected: 30n },
    { input: new Uint8Array([10, 20, 30]), args: [3n], expected: 0n },
  ];

  for (const testCase of byteAtOrZeroCases) {
    const actual = callByteArray(byteAtOrZero, testCase.input, testCase.args);
    if (actual !== testCase.expected) {
      throw new Error(`byteAtOrZero: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const emptyViaIsEmpty = await instantiate("emptyViaIsEmpty");
  const emptyViaIsEmptyCases = [
    { input: new Uint8Array([]), expected: 1n },
    { input: new Uint8Array([1]), expected: 0n },
  ];

  for (const testCase of emptyViaIsEmptyCases) {
    const actual = callByteArray(emptyViaIsEmpty, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`emptyViaIsEmpty: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const total =
    firstBytePlusArrayCases.length +
    firstByteIsStarCases.length +
    firstByteNextIsZeroCases.length +
    firstByteLowNibbleCases.length +
    firstByteBangIndexCases.length +
    byteAtOrZeroCases.length +
    emptyViaIsEmptyCases.length;
  process.stdout.write(`checked ${total} bytearray allocation cases\n`);
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
