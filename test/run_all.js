#!/usr/bin/env node

const path = require("path");
const { spawnSync } = require("child_process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const fuzzCases = process.env.LEANEXE_FUZZ_CASES || "50";

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8", stdio: "inherit" });
  if (result.status !== 0) {
    throw new Error(`${args.join(" ")} failed`);
  }
}

function main() {
  run(["lake", "build"]);
  run(["lake", "build", "LeanExe.Examples.Correctness"]);
  run(["node", path.join("test", "report_classification.js")]);
  run(["node", path.join("test", "core_correctness.js")]);
  run(["node", path.join("test", "bytearray_alloc.js")]);
  run([
    "node",
    path.join("test", "fuzz_validate.js"),
    path.join(".lake", "build", "ascii-generic.wasm"),
    fuzzCases,
  ]);
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
