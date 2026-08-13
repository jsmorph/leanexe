#!/usr/bin/env node
"use strict";

const {
  classifyKnownIssues,
  leanPublicImports,
  mathlibTacticSource,
  parseClassifierOutput,
  parseTalosCounts,
  parseTalosFailures,
  requireExactFile,
  selectValidatorCommand,
} = require("../tools/artifact-conformance");

const expectedMathlibTacticSuffix = [
  "proofs", "talos", "lean", ".lake", "packages", "mathlib", "Mathlib", "Tactic.lean",
].join(require("node:path").sep);
if (!mathlibTacticSource.endsWith(expectedMathlibTacticSuffix) ||
    mathlibTacticSource.includes(`${require("node:path").sep}CodeLib${require("node:path").sep}`)) {
  throw new Error("conformance uses a dependency cache outside the proof workspace");
}

const publicImports = leanPublicImports(`
module
/- public import Hidden.One
  /- public import Hidden.Two -/
-/
public import Example.One Example.Two -- trailing comment
public import Example.Three
private import Example.Private
`);
if (JSON.stringify(publicImports) !== JSON.stringify([
  "Example.One",
  "Example.Two",
  "Example.Three",
])) {
  throw new Error("public Lean import parsing returned incorrect modules");
}

const counts = parseTalosCounts(
  "Totals: 45 pass  6 fail  0 skip  0 cascade  0 decode-err  0 interp-err  0 out-of-fuel",
);
if (counts.pass !== 45 || counts.fail !== 6 || counts.skip !== 0 ||
    counts.cascade !== 0 || counts.decodeError !== 0 ||
    counts.interpreterError !== 0 || counts.outOfFuel !== 0) {
  throw new Error("Talos totals parser returned incorrect counts");
}

const detail = [
  "  L49  assert_return   Fail  expected [i32:-1], got [i32:5]",
  "  L50  assert_return   Fail  expected [i32:5], got [i32:6]",
].join("\n");
const failures = parseTalosFailures(detail);
if (failures.length !== 2 || failures[0].line !== 49 ||
    failures[0].command !== "assert_return" ||
    failures[0].expected !== "[i32:-1]" || failures[0].actual !== "[i32:5]") {
  throw new Error("Talos failure parser returned incorrect rows");
}

const item = { name: "memory_grow.wast" };
const issue = {
  id: "talos-imported-memory-instance",
  file: item.name,
  failures,
};
const classified = classifyKnownIssues(
  item,
  { ...counts, fail: 2 },
  failures,
  [issue],
);
if (classified.error !== null || classified.warnings.length !== 1) {
  throw new Error("exact known Talos failures were not classified as a warning");
}
const resolved = classifyKnownIssues(item, { ...counts, fail: 0 }, [], [issue]);
if (resolved.error !== null || resolved.warnings.length !== 0) {
  throw new Error("resolved known Talos failures still produced a warning");
}
const changed = classifyKnownIssues(
  item,
  { ...counts, fail: 2 },
  [{ ...failures[0], actual: "[i32:6]" }, failures[1]],
  [issue],
);
if (changed.error === null || changed.warnings.length !== 0) {
  throw new Error("changed Talos failures were accepted as a known warning");
}
const incomplete = classifyKnownIssues(
  item,
  { ...counts, fail: 2 },
  [failures[0]],
  [issue],
);
if (incomplete.error === null) {
  throw new Error("missing Talos failure detail was accepted");
}

const validatorItem = {
  file: "align.wast",
  line: 310,
  command: "assert_invalid",
};
const validatorCommand = selectValidatorCommand([
  { type: "module", line: 1, filename: "align.0.wasm" },
  { type: "assert_invalid", line: 310, filename: "align.70.wasm" },
], validatorItem);
if (validatorCommand.filename !== "align.70.wasm") {
  throw new Error("official validator command selection returned the wrong module");
}
const classifications = parseClassifierOutput([
  "/tmp/one.wasm\tdecode\tWasm.Binary.ErrorKind.unexpectedEnd",
  "/tmp/two.wasm\tvalidation\tWasm.Binary.ValidationErrorKind.invalidMemoryLimits",
].join("\n"));
if (classifications.size !== 2 || classifications.get("/tmp/two.wasm").stage !== "validation") {
  throw new Error("artifact validator classifications were parsed incorrectly");
}

requireExactFile(["i64.wast", "v128_load.wast", "load.wast"], "i64.wast");
try {
  requireExactFile(["i64.wast", "v128_load.wast", "load.wast"], "missing.wast");
} catch (error) {
  if (!error.message.includes("missing.wast") || !error.message.includes("absent")) throw error;
  process.stdout.write(
    "checked conformance parsing, known issues, official validator cases, and file selection\n",
  );
  process.exit(0);
}
throw new Error("missing conformance file was accepted");
