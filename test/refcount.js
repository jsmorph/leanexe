#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");
const host = require("./wasmtime_host");

const correctnessModule = "LeanExe.Examples.Correctness";
const byteArrayModule = "LeanExe.Examples.ByteArrayPrograms";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "refcount");

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args.join(" ")} failed`);
  }
  return result.stdout.trim();
}

function compile(moduleName, entry) {
  const out = path.join(outDir, `${moduleName}.${entry}.wasm`);
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
  return out;
}

function runHost(args) {
  run([host.ensureHost(), ...args]);
}

function expectI64(moduleName, entry, expected, args = []) {
  const wasm = compile(moduleName, entry);
  const actual = host.callI64(wasm, entry, args);
  if (actual !== BigInt(expected)) {
    throw new Error(`${entry}: expected ${expected}, got ${actual}`);
  }
}

function checkRuntimeApiReuse() {
  const structureArray = compile(correctnessModule, "structureArrayReturn");
  runHost(["release-reuse", structureArray, "structureArrayReturn", "2", "0", "16"]);
  runHost(["retain-delay", structureArray, "structureArrayReturn", "2", "0", "16"]);

  const byteArray = compile(correctnessModule, "byteArrayStringConstReturn");
  runHost(["free-alias", byteArray, "byteArrayStringConstReturn", "58595a"]);

  const grows = compile(correctnessModule, "byteArrayStringConstReturn");
  runHost(["allocator-grows", grows]);
}

function checkCompilerReleasesScalarTemp() {
  const wasm = compile(byteArrayModule, "firstBytePlusArray");
  runHost(["temp-byte-call", wasm, "firstBytePlusArray", "25", "42", "16"]);
}

function checkSourceReleaseStats() {
  const cases = [
    ["byteArrayStructReplicateRuntimeReleaseFrees", 202],
    ["nestedArrayRuntimeReleaseFrees", 202],
    ["structArrayFieldRuntimeReleaseFrees", 202],
    ["optionByteArrayArrayRuntimeReleaseFrees", 302],
    ["publicTokenArrayRuntimeReleaseFrees", 302],
    ["byteArrayGroupArrayRuntimeReleaseFrees", 403],
  ];
  for (const [entry, expected] of cases) {
    expectI64(correctnessModule, entry, expected);
  }
  const recursiveCases = [
    [0, 101],
    [1, 707],
    [2, 707],
  ];
  for (const [kind, expected] of recursiveCases) {
    expectI64(correctnessModule, "recursiveScenarioRuntimeReleaseStats", expected, [host.i64(kind)]);
    expectI64(correctnessModule, "recursiveScenarioHelperRuntimeReleaseStats", expected, [host.i64(kind)]);
  }
  expectI64(correctnessModule, "sharedRecursiveChildReleaseStats", 10302);
}

function checkBorrowedArrayNoopRelease() {
  const cases = [
    ["borrowedArrayPopEmptyReleaseFrees", [], 0],
    ["borrowedArraySetOobReleaseFrees", [7, 8], 0],
    ["borrowedArrayReverseSingletonReleaseFrees", [7], 0],
  ];
  for (const [entry, values, expected] of cases) {
    expectI64(correctnessModule, entry, expected, [host.arrayU64(values)]);
  }
}

function checkCompilerReleasesOwnedCallResults() {
  const noargCases = [
    ["ownedArrayCallTempScalar", 5, "16"],
    ["ownedByteArrayCallTempScalar", 66, "1"],
    ["ownedRecursiveNodeParamCallTempScalar", 310, "32,32,32"],
    ["ownedBoxCallTempScalar", 13, "16,1"],
  ];
  for (const [entry, expected, sizes] of noargCases) {
    const wasm = compile(correctnessModule, entry);
    runHost(["noarg-temp-reuse", wasm, entry, String(expected), sizes]);
  }

  const arrayParam = compile(correctnessModule, "ownedArrayParamCallTempScalarFromInput");
  runHost(["temp-array-call", arrayParam, "ownedArrayParamCallTempScalarFromInput", "5", "16", "24"]);

  const bytesParam = compile(correctnessModule, "ownedByteArrayParamCallTempScalarFromInput");
  runHost(["temp-byte-call", bytesParam, "ownedByteArrayParamCallTempScalarFromInput", "41", "100", "2"]);

  expectI64(correctnessModule, "byteArrayResultDropsOwnedTempStats", 10101);
}

function checkCompilerReleasesFoldAccumulators() {
  const cases = [
    ["arrayFoldByteArrayAccumulatorReleaseStats", 30202],
    ["arrayFoldOptionByteArrayAccumulatorReleaseStats", 30502],
    ["arrayFoldPublicTokenAccumulatorReleaseStats", 30402],
    ["arrayFoldByteArrayGroupAccumulatorReleaseStats", 30502],
    ["byteArrayFoldByteArrayAccumulatorReleaseStats", 30202],
    ["idRunByteArrayForOutputReleaseStats", 30202],
    ["idRunRangeForByteArrayOutputReleaseStats", 30202],
    ["arrayFoldRecursiveAccumulatorReleaseStats", 30606],
  ];
  for (const [entry, expected] of cases) {
    expectI64(correctnessModule, entry, expected);
  }

  expectI64(
    correctnessModule,
    "arrayFoldInputByteArrayAccumulatorReleaseStats",
    30202,
    [host.arrayU64([65, 66, 67])],
  );
  expectI64(
    correctnessModule,
    "byteArrayFoldInputByteArrayAccumulatorReleaseStats",
    30202,
    [host.byteArray(new Uint8Array([1, 2, 3]))],
  );
}

function main() {
  run(["lake", "build", correctnessModule]);
  run(["lake", "build", byteArrayModule]);
  fs.mkdirSync(outDir, { recursive: true });
  checkRuntimeApiReuse();
  checkCompilerReleasesScalarTemp();
  checkSourceReleaseStats();
  checkBorrowedArrayNoopRelease();
  checkCompilerReleasesOwnedCallResults();
  checkCompilerReleasesFoldAccumulators();
  process.stdout.write("checked 38 refcount cases\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
