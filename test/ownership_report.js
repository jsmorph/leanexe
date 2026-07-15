#!/usr/bin/env node

const path = require("path");
const { runChecked } = require("../tools/run-process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const correctnessModule = "LeanExe.Examples.Correctness";

function run(args) {
  const result = runChecked(args, { encoding: "utf8" });
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

function exportSection(report, exportName) {
  const marker = `export: ${exportName}`;
  const markerIndex = report.indexOf(marker);
  if (markerIndex < 0) {
    throw new Error(`${exportName}: missing export section`);
  }
  const start = report.lastIndexOf("\n[", markerIndex);
  const end = report.indexOf("\n[", markerIndex + marker.length);
  return report.slice(start < 0 ? markerIndex : start, end < 0 ? report.length : end);
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

function checkSourceReleaseJudgments() {
  const cases = [
    ["unusedRecursiveRuntimeReleaseFrees", "tree: direct fresh allocation"],
    [
      "recursiveScenarioHelperRuntimeReleaseStats",
      "tree: fresh helper result from LeanExe.Examples.Correctness.u64BinaryScenario",
    ],
    ["borrowedArraySetOobReleaseFrees", "updated: statically owner-zero array"],
  ];
  for (const [name, judgment] of cases) {
    const entry = `${correctnessModule}.${name}`;
    const report = ownershipReport(correctnessModule, entry);
    assertContains(report, "source release judgments: 1", entry);
    assertContains(report, judgment, entry);
  }
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

function checkExplicitRecursiveReleaseSuppressesCompilerRelease() {
  const entry = `${correctnessModule}.recursiveScenarioHelperRuntimeReleaseStats`;
  const report = ownershipReport(correctnessModule, entry);
  const section = exportSection(report, "recursiveScenarioHelperRuntimeReleaseStats");
  assertContains(section, "compiler statement releases: none", entry);
  assertContains(section, "explicit release expressions: 1", entry);
}

function main() {
  checkOptionByteArrayLoop();
  checkExceptByteArrayLoop();
  checkOptionByteArrayStateLoop();
  checkSourceReleaseJudgments();
  checkHeapBearingArrayFoldAccumulators();
  checkExplicitRecursiveReleaseSuppressesCompilerRelease();
  process.stdout.write("checked 10 ownership report cases\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
