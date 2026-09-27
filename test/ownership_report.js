#!/usr/bin/env node

const path = require("path");
const fs = require("node:fs");
const assert = require("node:assert/strict");
const { runChecked } = require("../tools/run-process");
const { callI64Slots, ensureHost } = require("../tools/wasmtime-host");

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
  assertContains(report, "compiler statement releases: 3", entry);
  assertContains(report, "byteArrayFoldMultiSlotAssign", entry);
  assertContains(report, "releaseOffsets=[1]", entry);
  assertOccurrenceCount(report, "byteArrayFoldMultiSlot", 1, entry);
}

function checkExceptByteArrayLoop() {
  const entry = `${correctnessModule}.exceptForByteArrayOutputReleaseStats`;
  const report = ownershipReport(correctnessModule, entry);
  assertContains(report, "entry: LeanExe.Examples.Correctness.exceptForByteArrayOutputReleaseStats", entry);
  assertContains(report, "compiler statement releases: 3", entry);
  assertContains(report, "resultWidth=5", entry);
  assertContains(report, "releaseOffsets=[2]", entry);
  assertContains(report, "byteArrayFoldMultiSlotAssign", entry);
  assertOccurrenceCount(report, "byteArrayFoldMultiSlot", 1, entry);
}

function checkOptionByteArrayStateLoop() {
  const entry = `${correctnessModule}.optionForByteArrayStateReleaseStats`;
  const report = ownershipReport(correctnessModule, entry);
  assertContains(report, "entry: LeanExe.Examples.Correctness.optionForByteArrayStateReleaseStats", entry);
  assertContains(report, "compiler statement releases: 3", entry);
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

function checkFreshArrayRelease() {
  const name = "flatArrayCopyRuntimeRelease";
  const entry = `${correctnessModule}.${name}`;
  const report = ownershipReport(correctnessModule, entry);
  assertContains(report, "original: direct fresh allocation", entry);
  const output = fs.mkdtempSync(path.join("tmp", "owned-array-copy-"));
  const binary = path.join(output, "copy.wasm");
  run([leanExe, "compile", "--module", correctnessModule, "--entry", entry, "--out", binary]);
  assert.deepEqual(callI64Slots(binary, name, 1, []), [202n]);
  const directName = "directFlatCopyRuntimeRelease";
  const direct = path.join(output, "direct.wasm");
  run([leanExe, "compile", "--module", correctnessModule,
    "--entry", `${correctnessModule}.${directName}`, "--out", direct]);
  assert.deepEqual(callI64Slots(direct, directName, 1, []), [75n]);
  for (const [helper, expected] of [
    ["flatArrayCallAppend", [3, 11, 21]],
    ["flatArrayConstantAppend", [7, 11, 13]],
  ]) {
    const wasm = path.join(output, `${helper}.wasm`);
    run([leanExe, "compile", "--module", correctnessModule,
      "--entry", `${correctnessModule}.${helper}`, "--out", wasm]);
    assert.deepEqual(JSON.parse(run([ensureHost(), "call", wasm, helper, "array-u64"])), expected);
  }
  for (const [rejected, binding] of [
    ["rejectReleaseFlatArrayAlias", "alias"],
    ["rejectReleaseFreshNestedArray", "held"],
    ["rejectReleaseDirectNestedMap", "heldMap"],
  ]) {
    assert.throws(() => ownershipReport(correctnessModule, `${correctnessModule}.${rejected}`),
      new RegExp(`reason: copied into heap-bearing binding ${binding}`));
  }
}

function checkInternalArrayLoop() {
  const name = "internalArrayLoopStats";
  const entry = `${correctnessModule}.${name}`;
  const output = fs.mkdtempSync(path.join("tmp", "internal-array-loop-"));
  const binary = path.join(output, "loop.wasm");
  run([leanExe, "compile", "--module", correctnessModule, "--entry", entry, "--out", binary]);
  for (const [fuel, skip, expected] of [
    [0n, 0n, [10n, 10n, 0n, 0n]],
    [1n, 0n, [11n, 10n, 0n, 0n]],
    [5n, 0n, [15n, 10n, 4n, 4n]],
    [5n, 1n, [12n, 10n, 1n, 1n]],
  ]) assert.deepEqual(callI64Slots(binary, name, 4, [fuel, skip]), expected);
}

function checkTailRelease() {
  const name = "tailArrayReleaseStats";
  const output = fs.mkdtempSync(path.join("tmp", "tail-array-release-"));
  const binary = path.join(output, "release.wasm");
  run([leanExe, "compile", "--module", correctnessModule,
    "--entry", `${correctnessModule}.${name}`, "--out", binary]);
  for (const [fuel, expected] of [[0n, 0n], [3n, 30303n]]) {
    assert.deepEqual(callI64Slots(binary, name, 1, [fuel]), [expected]);
  }
}

function checkFreshTailResult() {
  const name = "freshTailArrayRelease";
  const output = fs.mkdtempSync(path.join("tmp", "fresh-tail-array-"));
  const binary = path.join(output, "release.wasm");
  run([leanExe, "compile", "--module", correctnessModule,
    "--entry", `${correctnessModule}.${name}`, "--out", binary]);
  assert.deepEqual(callI64Slots(binary, name, 1, []), [101n]);
  run(["lake", "env", "lean", "test/fresh_owner_summary.lean"]);
}

function checkArrayMapSharing() {
  const output = fs.mkdtempSync(path.join("tmp", "array-map-sharing-"));
  for (const [name, expected] of [
    ["arrayMapHelperShared", [1n, 3n]],
    ["arrayMapInlineShared", [1n, 3n]],
    ["arrayMapEmptyShared", [2n]],
  ]) {
    const binary = path.join(output, name + ".wasm");
    run([leanExe, "compile", "--module", correctnessModule,
      "--entry", `${correctnessModule}.${name}`, "--out", binary]);
    assert.deepEqual(callI64Slots(binary, name, expected.length, []), expected);
  }
}

function checkNestedArrayUpdateLoop() {
  const name = "nestedArrayUpdateLoop";
  const output = fs.mkdtempSync(path.join("tmp", "nested-array-update-"));
  const binary = path.join(output, name + ".wasm");
  run([leanExe, "compile", "--module", correctnessModule,
    "--entry", `${correctnessModule}.${name}`, "--out", binary]);
  for (const rows of [0, 1, 2, 8]) {
    for (const columns of [0, 1, 4]) {
      const expected = Array(columns + 1).fill(0);
      for (let row = 0; row < rows; row++) {
        let carry = row;
        for (let column = 0; column < columns; column++) {
          carry += expected[column] + 1;
          expected[column] = carry;
        }
        expected[columns] = carry;
      }
      const [words, stats] = run([ensureHost(), "call-stats", binary, name,
        "array-u64", `i64:${rows}`, `i64:${columns}`]).trim().split("\n");
      assert.deepEqual(JSON.parse(words), expected);
      const [, allocations, , , frees] = stats.split(" ").map(Number);
      assert.equal(allocations - frees, 1,
        `${name}(${rows}, ${columns}): only the returned array should remain allocated`);
    }
  }
}

function checkNestedMonadicLoops() {
  const output = fs.mkdtempSync(path.join("tmp", "nested-monadic-loops-"));
  for (const monad of ["Option", "Except"]) {
    const name = `nested${monad}ArrayLoopStats`;
    const binary = path.join(output, name + ".wasm");
    run([leanExe, "compile", "--module", correctnessModule,
      "--entry", `${correctnessModule}.${name}`, "--out", binary]);
    for (const [rows, columns, stop, size, work] of [
      [0n, 4n, 0n, 0n, 0n],
      [3n, 4n, 0n, 15n, 15n],
      [3n, 4n, 1n, 0n, 0n],
      [3n, 4n, 7n, 0n, 7n],
    ]) {
      const [result, allocations] = callI64Slots(binary, name, 2, [rows, columns, stop]);
      assert.equal(result, monad === "Except" && stop > 0n ? stop : size);
      assert.equal(allocations, 1n + work,
        `${name}(${rows}, ${columns}, ${stop}): ${allocations} allocations for ${work} pushes`);
    }
  }
}

function checkConditionalIdArrayLoop() {
  const name = "conditionalIdArrayLoop";
  const output = fs.mkdtempSync(path.join("tmp", "conditional-id-loop-"));
  const binary = path.join(output, name + ".wasm");
  run([leanExe, "compile", "--module", correctnessModule,
    "--entries", `${correctnessModule}.${name},${correctnessModule}.${name}Stats`, "--out", binary]);
  for (const [count, stop] of [[0, 0], [1, 0], [8, 0], [8, 1], [8, 4], [8, 8]]) {
    const expected = [];
    let work = 0;
    for (let index = 0; index < count; index++) {
      expected.push(index);
      work++;
      if (expected.length === stop) break;
      if (index % 2 !== 0) {
        expected[0] = 99;
        work++;
      }
    }
    const [size, allocations] = callI64Slots(binary, `${name}Stats`, 2, [BigInt(count), BigInt(stop)]);
    assert.equal(size, BigInt(expected.length));
    assert.equal(allocations, BigInt(1 + work), `${name}(${count}, ${stop}): duplicated body evaluation`);
    const [words, stats] = run([ensureHost(), "call-stats", binary, name,
      "array-u64", `i64:${count}`, `i64:${stop}`]).trim().split("\n");
    assert.deepEqual(JSON.parse(words), expected);
    const [, allocated, , , freed] = stats.split(" ").map(Number);
    assert.equal(allocated - freed, 1, `${name}(${count}, ${stop}): unreleased intermediate array`);
  }
}

function main() {
  if (process.argv[2] === "--conditional") {
    checkConditionalIdArrayLoop();
    process.stdout.write("checked conditional Id loop results, allocations, and releases\n");
    return;
  }
  if (process.argv[2] === "--nested") {
    checkNestedArrayUpdateLoop();
    checkNestedMonadicLoops();
    process.stdout.write("checked nested loop results, allocations, and releases\n");
    return;
  }
  checkOptionByteArrayLoop();
  checkExceptByteArrayLoop();
  checkOptionByteArrayStateLoop();
  checkSourceReleaseJudgments();
  checkHeapBearingArrayFoldAccumulators();
  checkExplicitRecursiveReleaseSuppressesCompilerRelease();
  checkFreshArrayRelease();
  checkNestedArrayUpdateLoop();
  checkConditionalIdArrayLoop();
  checkInternalArrayLoop();
  checkTailRelease();
  checkFreshTailResult();
  checkArrayMapSharing();
  checkNestedMonadicLoops();
  process.stdout.write("checked ownership reports, array calls, and nested monadic loops\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
