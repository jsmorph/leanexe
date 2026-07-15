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
  run([process.execPath, path.join("tools", "check-node-version.js")]);
  run(["lake", "build"]);
  run(["lake", "build", "LeanExe"]);
  run(["lake", "build", "LeanExe.Examples.Correctness"]);
  run(["lake", "build", "LeanExe.Examples.ClobTest"]);
  run([
    "lake",
    "build",
    "LeanExe.Examples.ByteArrayPrograms",
    "LeanExe.Examples.JsonGcTreeRewrite",
    "LeanExe.Examples.JsonMergeTreeCommand",
    "LeanExe.Examples.JsonObjectArrayDecode",
    "LeanExe.Examples.JsonTypedDecode",
  ]);
  run([process.execPath, path.join("test", "report_classification.js")]);
  run([process.execPath, path.join("test", "ownership_report.js")]);
  run([process.execPath, path.join("test", "no_js_wasm_execution.js")]);
  run([process.execPath, path.join("test", "cli_errors.js")]);
  run([process.execPath, path.join("test", "core_correctness.js")]);
  run([process.execPath, path.join("test", "matched_values.js")]);
  run([process.execPath, path.join("test", "refcount.js")]);
  run([process.execPath, path.join("test", "bytearray_alloc.js")]);
  run([process.execPath, path.join("test", "asciistring.js")]);
  run([process.execPath, path.join("test", "intmap.js")]);
  run([process.execPath, path.join("test", "json_double.js")]);
  run([process.execPath, path.join("test", "wasi_program.js")]);
  run([process.execPath, path.join("test", "self_emit.js")]);
  run([process.execPath, path.join("tools", "compare-standard.js"), "--self-test"]);
  run([
    process.execPath,
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
