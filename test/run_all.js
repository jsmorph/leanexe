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
  run(["lake", "build", "LeanExe"]);
  run(["lake", "build", "LeanExe.Examples.Correctness"]);
  run(["node", path.join("test", "report_classification.js")]);
  run(["node", path.join("test", "ownership_report.js")]);
  run(["node", path.join("test", "no_js_wasm_execution.js")]);
  run(["node", path.join("test", "core_correctness.js")]);
  run(["node", path.join("test", "refcount.js")]);
  run(["node", path.join("test", "bytearray_alloc.js")]);
  run(["node", path.join("test", "asciistring.js")]);
  run(["node", path.join("test", "intmap.js")]);
  run(["node", path.join("test", "json_double.js")]);
  run(["node", path.join("test", "wasi_program.js")]);
  run(["node", path.join("test", "self_emit.js")]);
  run(["node", path.join("tools", "compare-standard.js"), "--self-test"]);
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
