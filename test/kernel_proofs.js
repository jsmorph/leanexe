#!/usr/bin/env node
// Kernel-check the universal source theorems and audit their transitive axioms.
// This is separate from the WASM execution tests; it proves no binary theorem.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const { runChecked } = require("../tools/run-process");
const run = (args, timeout = 90000) => runChecked(args, { encoding: "utf8", timeout }).stdout.trim();
const modules = ["SortProofs", "UniverseProofs"];
const names = [
  "checkSort_accept_iff", "checkSort_reject_iff", "checkSort_overflow_iff",
  "maxLevel_correct", "imaxLevel_correct", "checkMax_accept_iff", "checkIMax_accept_iff",
  "checkMax_reject_iff", "checkIMax_reject_iff", "checkLevelOp_unsupported",
].map(n => `LeanExe.KernelCheck.${n}`);
run([process.execPath, "tools/check-node-version.js"]);
run(["lake", "build", ...modules.map(m => `LeanExe.KernelCheck.${m}`)]);
const dir = ".lake/build/kernel-check";
fs.mkdirSync(dir, { recursive: true });
const file = `${dir}/ProofAudit.lean`;
fs.writeFileSync(file, modules.map(m => `import LeanExe.KernelCheck.${m}`).join("\n") + "\n" +
  names.map(n => `#print axioms ${n}`).join("\n") + "\n");
const output = run(["lake", "env", "lean", file]);
const allowed = new Set(["propext", "Classical.choice", "Quot.sound"]);
const reports = [...output.matchAll(/^'([^']+)' depends on axioms: \[([^\]]*)\]$/gm)];
assert.deepEqual(reports.map(m => m[1]), names, "one axiom report per theorem");
for (const [,name,list] of reports) {
  for (const axiom of list.split(",").map(s => s.trim()).filter(Boolean)) {
    assert(allowed.has(axiom), `${name} uses unapproved axiom ${axiom}`);
  }
}
console.log(`kernel-checked ${names.length} universal source theorems; axiom audit permits only propext, Classical.choice, Quot.sound`);
