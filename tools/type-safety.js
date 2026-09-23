#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");

const root = path.resolve(__dirname, "..");
const runner = path.join(root, "tools", "leanrun");
const auditedTheorems = [
  "lookup_lt",
  "tyWellFormed_iff",
  "typesWellFormed_iff",
  "constructorsWellFormed_iff",
  "declarationTableWellFormed_iff",
  "declarationsWellFormed_iff",
  "signatureWellFormed_iff",
  "signaturesWellFormed_iff",
  "TypesWF.append",
  "TypesWF.lookup",
  "ConstructorsWF.lookup",
  "DeclarationTableWF.lookup",
  "SignaturesWF.lookup",
  "TyWF.prod_left",
  "TyWF.prod_right",
  "TyWF.sum_left",
  "TyWF.sum_right",
  "TyWF.array_item",
  "BodiesTyped.lookup",
  "EnvTyped.append",
  "EnvTyped.lookup",
  "ValueTyped.wellFormed",
  "ValuesTyped.wellFormed",
  "EnvTyped.wellFormed",
  "EnvTyped.length",
  "ExprTyped.wellFormed",
  "ArgsTyped.wellFormed",
  "BranchesTyped.lookup",
  "BranchesTyped.length",
  "ValueTyped.bool_canonical",
  "ValueTyped.unit_canonical",
  "ValueTyped.nat_canonical",
  "ValueTyped.prod_canonical",
  "ValueTyped.sum_canonical",
  "ValueTyped.array_canonical",
  "ValueTyped.data_canonical",
  "ArrayValues.lookup_none_iff",
  "ArrayValues.lookup_append_left",
  "ArrayValues.lookup_append_right",
  "ArrayValues.replace_none_iff",
  "ArrayValues.replace_length",
  "ArrayValues.replace_lookup_same",
  "ArrayValues.replace_lookup_other",
  "ArrayValues.get_failure_iff",
  "ArrayValues.set_failure_iff",
  "ArrayValues.push_failure_iff",
  "ArrayValues.append_failure_iff",
  "ArrayValues.set_success_iff",
  "ArrayValues.set_success_length",
  "ArrayValues.get_after_set_same",
  "ArrayValues.get_after_set_other",
  "ArrayValues.push_success",
  "ArrayValues.append_success",
  "ArrayValues.push_success_iff",
  "ArrayValues.append_success_iff",
  "ArrayValues.push_success_length",
  "ArrayValues.append_success_length",
  "ArrayValues.get_after_push_last",
  "ArrayValues.get_after_append_left",
  "ArrayValues.get_after_append_right",
  "ValuesTyped.append",
  "ValuesTyped.lookup",
  "ValuesTyped.replace",
  "ArrayValues.empty_typed",
  "ArrayValues.get_typed",
  "ArrayValues.set_typed",
  "ArrayValues.push_typed",
  "ArrayValues.append_typed",
  "FrameTyped.wellFormed",
  "KontTyped.wellFormed",
  "StateTyped.wellFormed",
  "initial_typed",
  "step_deterministic",
  "enter_call_typed",
  "eval_step_typed",
  "frame_step_typed",
  "safety_step",
  "terminal_no_step",
  "preservation",
  "progress",
  "preservation_steps",
  "typed_not_stuck",
  "type_safety",
  "closed_type_safety",
  "return_type",
  "overflow_is_justified",
  "usesArgs_iff",
  "usesBranches_iff",
  "parametersUsed_iff",
  "admissible_let_iff",
  "admissible_split_iff",
  "admissible_sumCase_iff",
  "admissible_unitCase_iff",
  "admissibleArgs_iff",
  "admissibleBranches_iff",
  "admissible_dataCtor_iff",
  "admissible_dataCase_iff",
  "programAdmissible_cons_iff",
  "programAdmissible_length",
  "programAdmissible_lookup",
  "profile_type_safety",
  "profile_return_type",
  "profile_overflow_is_justified",
].map(name => `LeanExe.TypeSafety.${name}`);
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
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_arrays.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_data.lean"]);

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
  const failures = [];
  for (const name of auditedTheorems) {
    if (!dependencies.has(name)) {
      failures.push(`Missing axiom audit result for ${name}`);
      continue;
    }
    const unexpected = dependencies.get(name).filter(axiom => !allowedAxioms.has(axiom));
    if (unexpected.length) failures.push(`${name} uses unexpected axioms: ${unexpected.join(", ")}`);
    console.log(`${name}: ${dependencies.get(name).join(", ") || "no axioms"}`);
  }
  if (failures.length) throw new Error(failures.join("\n"));
  console.log(`Type-safety gate passed: core build, behavior checks, ${auditedTheorems.length} theorem audits.`);
}

try {
  main();
} catch (error) {
  console.error(`type-safety: ${error.message}`);
  process.exit(1);
}
