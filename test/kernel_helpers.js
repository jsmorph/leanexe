// Common test preparation only. All checker decisions execute in Lean/WASM.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");
const dir = ".lake/build/kernel-check";
const run = (args, timeout = 60000) => runChecked(args, { encoding: "utf8", timeout }).stdout.trim();
function compile(module, entry, checkpoint) {
  run([process.execPath, "tools/check-node-version.js"]);
  run(["lake", "build", `LeanExe.KernelCheck.${module}Test`, "lean-wasm"], 900000);
  fs.mkdirSync(dir, { recursive: true });
  const artifact = `${dir}/checker-${checkpoint}.wasm`;
  run([process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm", "compile",
    "--module", `LeanExe.KernelCheck.${module}`, "--entry", `LeanExe.KernelCheck.${entry}`,
    "--out", artifact], 90000);
  return artifact;
}
const leanArray = values => `#[${values.join(", ")}]`;
function reference(module, expressions) {
  const file = `${dir}/${module}Reference.lean`;
  fs.writeFileSync(file, `import LeanExe.KernelCheck.${module}\nopen LeanExe.KernelCheck\n` +
    expressions.map(e => `#eval ${e}`).join("\n") + "\n");
  const lines = run(["lake", "env", "lean", file]).split(/\r?\n/);
  assert.equal(lines.length, expressions.length, "standard Lean result count");
  return lines;
}
module.exports = { assert, fs, host, run, compile, leanArray, reference, dir };
