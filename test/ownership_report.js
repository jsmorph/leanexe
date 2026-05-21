#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const correctnessModule = "LeanExe.Examples.Correctness";

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args.join(" ")} failed`);
  }
  return result.stdout;
}

function assertContains(text, needle, label) {
  if (!text.includes(needle)) {
    throw new Error(`${label}: missing ${needle}`);
  }
}

function countOccurrences(text, needle) {
  return text.split(needle).length - 1;
}

function assertOccurrenceCount(text, needle, expected, label) {
  const actual = countOccurrences(text, needle);
  if (actual !== expected) {
    throw new Error(`${label}: expected ${expected} occurrences of ${needle}, got ${actual}`);
  }
}

function ownershipReport(moduleName, entryName) {
  return run([
    leanExe,
    "ownership-report",
    "--module",
    moduleName,
    "--entry",
    entryName,
  ]);
}

function checkOptionByteArrayLoop() {
  const entry = `${correctnessModule}.optionForByteArrayOutputReleaseStats`;
  const report = ownershipReport(correctnessModule, entry);
  assertContains(report, "LeanExe ownership report", entry);
  assertContains(report, "entry: LeanExe.Examples.Correctness.optionForByteArrayOutputReleaseStats", entry);
  assertContains(report, "compiler statement releases: 2", entry);
  assertContains(report, "byteArrayFoldMultiSlotAssign", entry);
  assertContains(report, "releaseOffsets=[1]", entry);
  assertOccurrenceCount(report, "byteArrayFoldMultiSlot", 1, entry);
}

function checkExceptByteArrayLoop() {
  const entry = `${correctnessModule}.exceptForByteArrayOutputReleaseStats`;
  const report = ownershipReport(correctnessModule, entry);
  assertContains(report, "entry: LeanExe.Examples.Correctness.exceptForByteArrayOutputReleaseStats", entry);
  assertContains(report, "compiler statement releases: 2", entry);
  assertContains(report, "resultWidth=5", entry);
  assertContains(report, "releaseOffsets=[2]", entry);
  assertContains(report, "byteArrayFoldMultiSlotAssign", entry);
  assertOccurrenceCount(report, "byteArrayFoldMultiSlot", 1, entry);
}

function checkOptionByteArrayStateLoop() {
  const entry = `${correctnessModule}.optionForByteArrayStateReleaseStats`;
  const report = ownershipReport(correctnessModule, entry);
  assertContains(report, "entry: LeanExe.Examples.Correctness.optionForByteArrayStateReleaseStats", entry);
  assertContains(report, "compiler statement releases: 2", entry);
  assertContains(report, "resultWidth=5", entry);
  assertContains(report, "releaseOffsets=[2]", entry);
  assertContains(report, "byteArrayFoldMultiSlotAssign", entry);
  assertOccurrenceCount(report, "byteArrayFoldMultiSlot", 1, entry);
}

function checkJsonTreeOutFile() {
  const out = path.join(".lake", "build", "ownership-report", "json-tree.txt");
  run([
    leanExe,
    "ownership-report",
    "--module",
    "LeanExe.Examples.JsonTreeCommand",
    "--entry",
    "LeanExe.Examples.JsonTreeCommand.makeTree",
    "--out",
    out,
  ]);
  const report = fs.readFileSync(out, "utf8");
  assertContains(report, "LeanExe.Examples.JsonTreeCommand.insertOwned", "JsonTreeCommand.makeTree");
  assertContains(report, "explicit release expressions: 1", "JsonTreeCommand.makeTree");
  assertContains(report, "helper fresh result owner offsets: [0]", "JsonTreeCommand.makeTree");
}

function checkHeapBearingArrayFoldAccumulators() {
  const cases = [
    `${correctnessModule}.arrayFoldOptionByteArrayAccumulatorReleaseStats`,
    `${correctnessModule}.arrayFoldPublicTokenAccumulatorReleaseStats`,
    `${correctnessModule}.arrayFoldByteArrayGroupAccumulatorReleaseStats`,
  ];
  for (const entry of cases) {
    const report = ownershipReport(correctnessModule, entry);
    assertContains(report, `entry: ${entry}`, entry);
    assertContains(report, "arrayFoldMultiSlotAssign", entry);
    assertContains(report, "releaseOffsets=[0]", entry);
    assertOccurrenceCount(report, "arrayFoldMultiSlotAssign", 1, entry);
  }
}

function main() {
  checkOptionByteArrayLoop();
  checkExceptByteArrayLoop();
  checkOptionByteArrayStateLoop();
  checkJsonTreeOutFile();
  checkHeapBearingArrayFoldAccumulators();
  process.stdout.write("checked 7 ownership report cases\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
