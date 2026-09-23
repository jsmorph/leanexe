#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");

const root = path.resolve(__dirname, "..");
const runner = path.join(root, "tools", "leanrun");
const auditedTheorems = [
  "WordWidth.modulus_pos",
  "WordWidth.modulus_mono",
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
  "evalNatBin_value_iff",
  "evalNatBin_overflow_iff",
  "evalNatBin_no_overflow",
  "evalNatBin_bounded",
  "evalNatBin_sub_saturates",
  "evalNatBin_div_zero",
  "evalNatBin_mod_zero",
  "NatCmpOp.eq_iff",
  "NatCmpOp.lt_iff",
  "NatCmpOp.le_iff",
  "bitAt_zero",
  "bitAt_succ",
  "bitCons_div_two",
  "bitCons_mod_two",
  "bitAt_bitCons_zero",
  "bitAt_bitCons_succ",
  "bitCons_reconstruct",
  "bitwiseBits_bounded",
  "bitwiseBits_bitAt",
  "eq_of_bitAt_eq",
  "bitAt_zero_value",
  "bitwiseBits_all_ones",
  "bitAt_mask",
  "WordWidth.modulus_le_nat64",
  "normalizeWord_eq",
  "normalizeWord_bounded",
  "normalizeWord_eq_self_iff",
  "normalizeWord_idempotent",
  "normalizeWord_widen",
  "normalizeWord_roundtrip",
  "wordToNat_bounded",
  "evalWordBin_bounded",
  "evalWordBin_add_eq",
  "evalWordBin_add_no_wrap",
  "evalWordBin_add_wrap",
  "evalWordBin_sub_eq",
  "evalWordBin_sub_no_underflow",
  "evalWordBin_sub_underflow",
  "evalWordBin_mul_eq",
  "evalWordBin_mul_no_wrap",
  "evalWordBin_div_eq",
  "evalWordBin_mod_eq",
  "evalWordBin_div_zero",
  "evalWordBin_mod_zero",
  "evalWordBin_div_mod",
  "evalWordBin_min_left",
  "evalWordBin_min_right",
  "evalWordBin_max_left",
  "evalWordBin_max_right",
  "WordWidth.bits_pos",
  "wordMask_bounded",
  "wordMask_bitAt",
  "evalWordBin_bitAnd_bitAt",
  "evalWordBin_bitOr_bitAt",
  "evalWordBin_bitXor_bitAt",
  "evalWordBin_bitAnd_zero",
  "evalWordBin_bitOr_zero",
  "evalWordBin_bitXor_zero",
  "evalWordBin_bitAnd_self",
  "evalWordBin_bitOr_self",
  "evalWordBin_bitXor_self",
  "evalWordBin_bitAnd_mask",
  "evalWordBin_bitOr_mask",
  "evalWordBin_bitXor_cancel",
  "evalWordBin_complement_bitAt",
  "evalWordBin_complement_involution",
  "shiftAmount_lt",
  "shiftAmount_periodic",
  "shiftAmount_zero",
  "shiftAmount_width",
  "evalWordBin_shiftLeft_eq",
  "evalWordBin_shiftRight_eq",
  "evalWordBin_shiftLeft_zero",
  "evalWordBin_shiftRight_zero",
  "evalWordBin_shiftLeft_width",
  "evalWordBin_shiftRight_width",
  "ExprTyped.add",
  "ExprTyped.succ",
  "ExprTyped.pred",
  "ExprTyped.boolToNat",
  "ExprTyped.wordNot",
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
  "ValueTyped.word_canonical",
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
  "step_add",
  "step_succ",
  "step_pred",
  "step_wordNot",
  "step_boolToNat",
  "step_natCase",
  "step_natCase_zero",
  "step_natCase_succ",
  "Steps.trans",
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
  "uses_natCase",
  "uses_natCase_iff",
  "uses_wordNot",
  "admissible_wordNot",
  "usesArgs_iff",
  "usesBranches_iff",
  "parametersUsed_iff",
  "admissible_let_iff",
  "admissible_split_iff",
  "admissible_sumCase_iff",
  "admissible_natCase_iff",
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
  "inferRaw_complete",
  "checkArgsRaw_complete",
  "checkBranchesRaw_complete",
  "inferRaw_sound",
  "checkArgsRaw_sound",
  "checkBranchesRaw_sound",
  "inferRaw_iff",
  "checkArgsRaw_iff",
  "checkBranchesRaw_iff",
  "ExprTyped.unique",
  "infer_eq_some_iff",
  "inferRaw_add",
  "inferRaw_succ",
  "inferRaw_pred",
  "inferRaw_boolToNat",
  "inferRaw_wordNot",
  "bodiesWellTyped_iff",
  "programWellTyped_iff",
  "profileExpressionWellTyped_iff",
  "profileProgramWellTyped_iff",
  "checked_type_safety",
  "profile_checked_type_safety",
  "ExprTyped.boolNot",
  "BoolBinOp.body_typed",
  "ExprTyped.boolBin",
  "inferRaw_boolNot",
  "BoolBinOp.inferRaw_body",
  "inferRaw_boolBin",
  "uses_boolNot",
  "admissible_boolNot",
  "BoolBinOp.body_uses_left",
  "BoolBinOp.body_uses_right",
  "BoolBinOp.body_closed",
  "BoolBinOp.body_admissible",
  "uses_boolBin",
  "admissible_boolBin",
  "step_boolNot",
  "step_boolBin",
  "boolBin_left_stage",
  "step_boolBin_right_stage",
  "boolNot_result_steps",
  "BoolBinOp.body_result_steps",
  "boolBin_result_steps",
  "boolNot_value_steps",
  "boolBin_value_steps",
  "valueEq_sound",
  "valuesEq_sound",
  "valueEq_refl",
  "valuesEq_refl",
  "valueEq_eq_true_iff",
  "valuesEq_eq_true_iff",
  "valueEq_eq_false_iff",
  "valuesEq_eq_false_iff",
  "valueEq_symm",
  "valuesEq_symm",
  "valueEq_pair",
  "valueEq_word",
  "valueEq_sum_tags",
  "valueEq_array",
  "valueEq_data",
  "valuesEq_nil_left",
  "valuesEq_nil_right",
  "valuesEq_cons",
  "valuesEq_length",
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
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_typing.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_naturals.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_words.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_bits.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_nat_case.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_booleans.lean"]);
  run(["lake", "env", "lean", "-DwarningAsError=true", "test/type_safety_value_equality.lean"]);

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
