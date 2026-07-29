#!/usr/bin/env node
"use strict";

// Runs the compiled LEB128 encoder against the false theorem in
// proofs/talos/lean/Examples/BogusArtifactClaim.lean.  That theorem is
// kernel-checked and claims the export returns length 1 for input 300.
// This script executes the same artifact the theorem describes.

const fs = require("fs");
const path = require("path");

const repoRoot = path.join(__dirname, "..");
const wasmPath = path.join(
  repoRoot, "proofs", "talos", ".generated", "leb_u32", "program.wasm");

const INPUT = 300n;
const CLAIMED_LENGTH = 1n;

function main() {
  if (!fs.existsSync(wasmPath)) {
    throw new Error(
      `artifact not found at ${wasmPath}; run tools/talos-artifact.js prepare leb_u32`);
  }
  const instance = new WebAssembly.Instance(
    new WebAssembly.Module(fs.readFileSync(wasmPath)), {});
  const [pointer, length] = instance.exports.u32lebU64(INPUT);
  const memory = new Uint8Array(instance.exports.memory.buffer);
  const bytes = Array.from(
    memory.slice(Number(pointer), Number(pointer) + Number(length)));
  const rendered = bytes.map((b) => `0x${b.toString(16).padStart(2, "0")}`).join(" ");

  console.log(`input: ${INPUT}`);
  console.log(`theorem Examples.BogusArtifactClaim.u32lebU64_bogus claims length ${CLAIMED_LENGTH}`);
  console.log(`artifact returns length ${length} with bytes ${rendered}`);

  if (length === CLAIMED_LENGTH) {
    throw new Error(
      "the artifact matched the false claim; the exhibit no longer demonstrates anything");
  }
  console.log("execution refutes the kernel-checked theorem");
}

try {
  main();
} catch (error) {
  console.error(`kernel_unsoundness_exhibit.js: ${error.message}`);
  process.exit(1);
}
