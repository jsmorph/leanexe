#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { checkBenchmark } = require("../tools/leanexegen-benchmark");

const repoRoot = path.resolve(__dirname, "..");
const benchmarkRoot = path.join(
  repoRoot, "benchmarks", "leanexegen", "demo1-array");
const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), "leanexegen-benchmark-test-"));

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

try {
  const checked = checkBenchmark(benchmarkRoot);
  assert(checked.referenceRun === "timing-2",
    "benchmark check returned the wrong reference run");
  assert(checked.runs.length === 10,
    "benchmark check returned the wrong number of retained runs");
  assert(checked.comparison.baselineVariant === "fixed-array-allocator" &&
    checked.comparison.candidateVariant === "fixed-array-singleton",
  "benchmark check returned the wrong comparison");
  const copy = path.join(temporaryRoot, "demo1-array");
  fs.cpSync(benchmarkRoot, copy, { recursive: true });
  fs.appendFileSync(path.join(copy, "allocator-2", "program.proof", "request.txt"), "changed\n");
  let rejected = false;
  try {
    checkBenchmark(copy);
  } catch (error) {
    rejected = error instanceof Error;
  }
  assert(rejected, "benchmark check accepted a modified frozen request");
  process.stdout.write("leanexegen benchmark identity tests passed\n");
} finally {
  fs.rmSync(temporaryRoot, { recursive: true, force: true });
}
