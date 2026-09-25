#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const assert = require("node:assert/strict");
const { runChecked } = require("./run-process");
const { certificates } = require("./byte-io-kernel");
const { embeddedSource, byteLookupSource, auditAxioms } = require("./byte-io-proof");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const moduleRoot = path.join(proofRoot, "Project/RunningSum");
const fixturePath = "proofs/running-sum/running-sum.wasm";
const fixture = path.join(root, fixturePath);
const source = "LeanExe.Examples.RunningSum";
const entry = `${source}.main`;
const embedding = { project: "RunningSum", fixturePath, entry, generator: "tools/running-sum-proof.js" };

function lean(args, options = {}) {
  return runChecked(["lake", "-d", proofRoot, ...args], {
    cwd: root, timeout: 120000, ...options,
  });
}

function compile() {
  runChecked(["lake", "build", "lean-wasm", source], {
    cwd: root, stdio: "inherit", timeout: 900000,
  });
  const fresh = path.join(root, "build/running-sum.wasm");
  runChecked([process.env.LEAN_WASM_EXE || path.join(root, ".lake/build/bin/lean-wasm"),
    "compile-wasi-io", "--module", source, "--entry", entry, "--out", fresh], {
    cwd: root, timeout: 120000,
  });
  return fresh;
}

function prepare() {
  const bytes = fs.readFileSync(compile());
  fs.mkdirSync(path.dirname(fixture), { recursive: true });
  fs.writeFileSync(fixture, bytes);
  fs.writeFileSync(path.join(moduleRoot, "ArtifactBytes.lean"), embeddedSource(bytes, embedding));
  fs.writeFileSync(path.join(moduleRoot, "ArtifactByteLookup.lean"), byteLookupSource(bytes, "RunningSum"));
  lean(["build", "Project.ByteIO.Binary", "Project.RunningSum.ArtifactBytes"], { stdio: "inherit" });
  const cache = lean(["env", "lean", "--run", path.join(moduleRoot, "GenerateCache.lean")],
    { encoding: "utf8", maxBuffer: 16 * 1024 * 1024 });
  assert.ok(cache.stdout.startsWith("import Project.ByteIO.Binary\n"), "invalid decoded cache");
  fs.writeFileSync(path.join(moduleRoot, "ArtifactCache.lean"), cache.stdout);
  const metadata = lean(["env", "lean", "--run",
    path.join(proofRoot, "Project/Artifact/Binary/CodeOffsets.lean"), fixture, "--nested"],
    { encoding: "utf8", maxBuffer: 16 * 1024 * 1024 });
  for (const [name, text] of certificates(bytes, metadata.stdout, "RunningSum")) {
    fs.writeFileSync(path.join(moduleRoot, `${name}.lean`), text);
  }
  console.log("Running-sum binary and decoding certificates prepared");
}

function checkTheorems(target, declarations, label, timeout = 120000) {
  lean(["build", `Project.RunningSum.${target}`], { stdio: "inherit", timeout });
  const names = declarations.map(name => `Project.RunningSum.${name}`);
  const audit = path.join(root, `work/running-sum/${target}Audit.lean`);
  fs.mkdirSync(path.dirname(audit), { recursive: true });
  fs.writeFileSync(audit, [`import Project.RunningSum.${target}`, ...names.map(name => `#print axioms ${name}`), ""].join("\n"));
  const result = lean(["env", "lean", audit], { encoding: "utf8" });
  auditAxioms(result.stdout, names);
  process.stdout.write(result.stdout);
  console.log(label);
}

function checkArithmetic() {
  checkTheorems("Render", ["add_correct", "parse_valid", "render_correct", "line_add_correct"],
    "Running-sum arithmetic proof passed");
}

function checkSource() {
  checkTheorems("SourceOrdering", ["add_correct", "parse_valid", "render_correct",
    "stream_correct", "consumeChunks_eq", "Source.main_eq", "Source.bytes_runs", "Source.main_correct",
    "Source.newline_correct"],
    "Running-sum Lean source proof passed");
}

function checkBinary() {
  const fresh = fs.readFileSync(compile());
  const bytes = fs.readFileSync(fixture);
  assert.ok(fresh.equals(bytes), "running-sum proof binary differs from compiler output");
  assert.equal(fs.readFileSync(path.join(moduleRoot, "ArtifactBytes.lean"), "utf8"), embeddedSource(bytes, embedding));
  assert.equal(fs.readFileSync(path.join(moduleRoot, "ArtifactByteLookup.lean"), "utf8"), byteLookupSource(bytes, "RunningSum"));
  checkTheorems("Artifact", ["decoded", "encoded", "validated", "valid", "imports_exact", "exports_exact"]
    .map(name => `Artifact.${name}`), "Running-sum binary decoding and validation proofs passed", 900000);
}

if (require.main === module) {
  const commands = { prepare, "check-arithmetic": checkArithmetic, "check-source": checkSource, "check-binary": checkBinary };
  const command = process.argv[2];
  if (process.argv.length !== 3 || !Object.hasOwn(commands, command)) {
    console.error("usage: tools/running-sum-proof.js <prepare | check-arithmetic | check-source | check-binary>");
    process.exit(2);
  }
  try { commands[command](); }
  catch (error) { console.error(error.stack || String(error)); process.exitCode = 1; }
}
