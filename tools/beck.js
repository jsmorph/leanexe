#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("./run-process");
const { ensureHost } = require("./wasmtime-host");

const root = path.resolve(__dirname, "..");
const moduleName = "LeanExe.Examples.Beck";
const wasm = path.join(root, "build/beck/beck.wasm");

function prepare() {
  runChecked(["lake", "build", "lean-wasm", moduleName],
    { cwd: root, encoding: "utf8", timeout: 900000 });
  fs.mkdirSync(path.dirname(wasm), { recursive: true });
  runChecked([path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", moduleName, "--entry", `${moduleName}.compute`, "--out", wasm],
  { cwd: root, encoding: "utf8", timeout: 120000 });
  ensureHost();
}

function encode(input) {
  if (!input || Array.isArray(input) || typeof input !== "object" ||
      Object.keys(input).some(key => key !== "categories" && key !== "jobs") ||
      !Number.isSafeInteger(input.categories) || input.categories < 0 ||
      !Array.isArray(input.jobs)) {
    throw new Error("expected {categories: nonnegative integer, jobs: array of membership arrays}");
  }
  const words = [input.jobs.length, input.categories];
  for (const membership of input.jobs) {
    if (!Array.isArray(membership) || membership.some(id => !Number.isSafeInteger(id) || id < 0)) {
      throw new Error("each job must contain nonnegative integer category IDs");
    }
    words.push(membership.length, ...membership);
  }
  return words;
}

function execute(words) {
  const text = runChecked([ensureHost(), "call", wasm, "compute", "array-u64",
    `array-u64:${words.join(",")}`],
  { cwd: root, encoding: "utf8", timeout: 60000 }).stdout.trim();
  const result = JSON.parse(text);
  if (!Array.isArray(result) || result.some(word => !Number.isSafeInteger(word) || word < 0)) {
    throw new Error("WASM returned an invalid word array");
  }
  return result;
}

function check(input, result) {
  if (result[0] !== 0) {
    if (result.length !== 1 || ![1, 2, 3].includes(result[0])) {
      throw new Error("WASM returned an invalid error result");
    }
    return { status: ["ok", "invalid-input", "capacity-limit", "internal-failure"][result[0]] };
  }
  if (result.length !== input.jobs.length + 2 || result.slice(2).some(group => group !== 0 && group !== 1)) {
    throw new Error("WASM returned invalid assignments");
  }
  const overlap = Math.max(0, ...input.jobs.map(job => job.length));
  if (result[1] !== overlap) throw new Error("WASM returned the wrong maximum overlap");
  const counts = Array.from({ length: input.categories }, (_, category) => ({ category, groups: [0, 0] }));
  input.jobs.forEach((membership, job) => {
    if (new Set(membership).size !== membership.length) throw new Error("WASM accepted duplicate membership");
    for (const category of membership) {
      if (category >= input.categories) throw new Error("WASM accepted an invalid category ID");
      counts[category].groups[result[job + 2]]++;
    }
  });
  const bound = overlap === 0 ? 0 : 2 * overlap - 1;
  for (const row of counts) {
    row.difference = Math.abs(row.groups[0] - row.groups[1]);
    if (row.difference > bound) throw new Error(`category ${row.category} exceeds discrepancy ${bound}`);
  }
  return { status: "ok", overlap, bound, assignments: result.slice(2), counts };
}

function main(args) {
  if (args.length === 1 && args[0] === "--help") {
    process.stdout.write("usage: tools/beck.js INPUT.json\nPrints WASM assignments and recomputed category counts.\n");
    return;
  }
  if (args.length !== 1) throw new Error("usage: tools/beck.js INPUT.json");
  const input = JSON.parse(fs.readFileSync(args[0], "utf8"));
  const words = encode(input);
  prepare();
  const result = check(input, execute(words));
  process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  if (result.status !== "ok") process.exitCode = 1;
}

if (require.main === module) {
  try { main(process.argv.slice(2)); }
  catch (error) {
    process.stderr.write(`beck: ${error.message}\n`);
    process.exitCode = 1;
  }
}

module.exports = { root, wasm, prepare, encode, execute, check };
