#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");

const root = path.resolve(__dirname, "..");
const runner = path.join(root, "tools", "leanrun");
const auditedTheorems = [
  "LeanExe.TypeSafety.preservation",
  "LeanExe.TypeSafety.progress",
  "LeanExe.TypeSafety.type_safety",
  "LeanExe.TypeSafety.closed_type_safety",
  "LeanExe.TypeSafety.return_type",
  "LeanExe.TypeSafety.overflow_is_justified",
  "LeanExe.TypeSafety.step_deterministic",
  "LeanExe.TypeSafety.profile_type_safety",
  "LeanExe.TypeSafety.profile_return_type",
  "LeanExe.TypeSafety.profile_overflow_is_justified",
  "LeanExe.TypeSafety.usesArgs_iff",
  "LeanExe.TypeSafety.parametersUsed_iff",
  "LeanExe.TypeSafety.admissible_let_iff",
  "LeanExe.TypeSafety.admissible_split_iff",
  "LeanExe.TypeSafety.admissible_sumCase_iff",
  "LeanExe.TypeSafety.admissible_unitCase_iff",
  "LeanExe.TypeSafety.admissibleArgs_iff",
  "LeanExe.TypeSafety.programAdmissible_cons_iff",
  "LeanExe.TypeSafety.programAdmissible_length",
  "LeanExe.TypeSafety.programAdmissible_lookup",
];
// Match the reviewed dependency set; expanding it requires an explicit review.
// In particular this rejects sorryAx, native evaluation certificates, and
// additional assumptions even when they are available in the Lean environment.
const allowedAxioms = new Set(["propext"]);

function run(args, capture = false) {
  const result = spawnSync(runner,
    ["--timeout", "120", "--lock-timeout", "30", ...args],
    { cwd: root, encoding: "utf8", stdio: capture ? "pipe" : "inherit" });
  if (result.error) throw result.error;
  if (result.status !== 0) {
    if (capture) {
      process.stdout.write(result.stdout || "");
      process.stderr.write(result.stderr || "");
    }
    throw new Error(`Lean check failed (${result.signal || result.status}): ${args.join(" ")}`);
  }
  return result.stdout || "";
}

function main() {
  if (process.argv.length !== 3 || process.argv[2] !== "check") {
    throw new Error("usage: tools/type-safety.js check");
  }
  const pin = fs.readFileSync(path.join(root, "lean-toolchain"), "utf8").trim();
  const expected = pin.match(/^leanprover\/lean4:v(.+)$/u)?.[1];
  if (!expected) throw new Error(`Unsupported toolchain pin: ${pin}`);
  const version = run(["lean", "--version"], true).trim();
  if (!version.startsWith(`Lean (version ${expected},`)) {
    throw new Error(`Expected ${pin}; found ${version}`);
  }
  console.log(version);

  run(["lake", "build", "LeanExe.TypeSafety"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_profile.lean"]);

  const auditDir = path.join(root, ".lake", "type-safety");
  fs.mkdirSync(auditDir, { recursive: true });
  const auditFile = path.join(auditDir, "Audit.lean");
  fs.writeFileSync(auditFile, "import LeanExe.TypeSafety\n\n" +
    auditedTheorems.map(name => `#print axioms ${name}`).join("\n") + "\n");
  const output = run(["lake", "env", "lean", "-DwarningAsError=true", ".lake/type-safety/Audit.lean"], true);
  const dependencies = new Map();
  for (const match of output.matchAll(/'([^']+)' depends on axioms:\s*\[([^\]]*)\]/gu)) {
    dependencies.set(match[1], match[2].split(",").map(x => x.trim()).filter(Boolean));
  }
  for (const match of output.matchAll(/'([^']+)' does not depend on any axioms/gu)) {
    dependencies.set(match[1], []);
  }
  for (const name of auditedTheorems) {
    if (!dependencies.has(name)) {
      throw new Error(`Missing axiom audit result for ${name}:\n${output}`);
    }
    const unexpected = dependencies.get(name).filter(axiom => !allowedAxioms.has(axiom));
    if (unexpected.length) throw new Error(`${name} uses unexpected axioms: ${unexpected.join(", ")}`);
    console.log(`${name}: ${dependencies.get(name).join(", ") || "no axioms"}`);
  }
  console.log(`Type-safety gate passed: core build, behavior checks, ${auditedTheorems.length} theorem audits.`);
}

try {
  main();
} catch (error) {
  console.error(`type-safety: ${error.message}`);
  process.exit(1);
}
