#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const {
  collectReleaseInputs,
  directExecutables,
  digestEntries,
  fixedInputs,
  localLeanImportClosure,
  proofSourceRoots,
  verificationDriverInputs,
} = require("../tools/artifact-identity");
const { currentLocalDate } = require("../tools/date");
const {
  leanImports,
  specificationInputs,
  talosBoundaryTarget,
} = require("../tools/artifact-proof");
const {
  leanSourcesUnder,
  verifierRelativeSources,
  verifierSourceSha256,
} = require("../tools/artifact-source");

const expectedSources = [
  "Syntax.lean",
  "Cursor.lean",
  "Leb.lean",
  "Primitives.lean",
  "Decode.lean",
  "Grammar.lean",
  "Validity.lean",
  "Validate.lean",
  "Translate.lean",
  "Equality.lean",
  "Evidence.lean",
  "Proof/Cursor.lean",
  "Proof/Leb.lean",
  "Proof/Primitives.lean",
  "Proof/Decode.lean",
  "Proof/Validate.lean",
  "Proof/Translate.lean",
];
if (JSON.stringify(verifierRelativeSources) !== JSON.stringify(expectedSources)) {
  throw new Error("the normative verifier source list changed without updating its test vector");
}

const repoRoot = path.resolve(__dirname, "..");
if (talosBoundaryTarget !== "Project.TalosPrelude") {
  throw new Error("the artifact proof gate no longer uses LeanExe's focused Talos boundary");
}
const expectedVerifierDigest = "bf03d3f47fb11563c947224601a21afa95c62fc88df81f493de821e69de9d1e7";
if (verifierSourceSha256(repoRoot) !== expectedVerifierDigest) {
  throw new Error("the normative verifier source digest changed without updating its test vector");
}

const entries = [
  { path: "b", bytes: Buffer.from("two") },
  { path: "a", bytes: Buffer.from("one") },
];
const expectedInputDigest = "8c9297a2b8fa8c929395d1202313fb1b5e28fa06dfdf6180500a5c95d7192ada";
if (digestEntries(entries) !== expectedInputDigest ||
    digestEntries([...entries].reverse()) !== expectedInputDigest) {
  throw new Error("release input hashing is not canonical");
}

const releaseInputs = collectReleaseInputs(repoRoot);
const releasePaths = new Set(releaseInputs.files.map((file) => file.path));
for (const required of [...fixedInputs, ...verificationDriverInputs]) {
  if (!releasePaths.has(required)) {
    throw new Error(`release identity omits ${required}`);
  }
}
for (const executable of directExecutables) {
  if (!releasePaths.has(executable)) {
    throw new Error(`release identity omits executable ${executable}`);
  }
}
const proofSources = leanSourcesUnder(repoRoot, proofSourceRoots);
for (const source of proofSources) {
  if (!releasePaths.has(source.relative)) {
    throw new Error(`release identity omits ${source.relative}`);
  }
}
const programSources = proofSources.filter((source) => source.relative.endsWith("/Program.lean"));
if (programSources.length !== 25) {
  throw new Error(`release identity found ${programSources.length} cached Talos programs`);
}
const localImports = localLeanImportClosure(repoRoot, [
  "proofs/talos/lean/Project.lean",
  ...proofSources.map((source) => source.relative),
]);
const expectedLocalImports = [
  "LeanExe/Examples/AsciiDigits.lean",
  "LeanExe/Examples/TalosAssocList.lean",
];
if (JSON.stringify(localImports) !== JSON.stringify(expectedLocalImports)) {
  throw new Error("the artifact proof's root-package import closure changed");
}
for (const imported of localImports) {
  if (!releasePaths.has(imported)) throw new Error(`release identity omits ${imported}`);
}

const parsedImports = leanImports(`
/- import Hidden.One
   /- import Hidden.Two -/
-/
prelude
import Example.One Example.Two -- trailing comment
import Example.Three
namespace Example
def text := "an apparent /- comment -/ and -- line comment"
`);
if (JSON.stringify(parsedImports) !== JSON.stringify([
  "Example.One",
  "Example.Two",
  "Example.Three",
])) {
  throw new Error("Lean import parsing failed its comment and multi-import test vector");
}

const specificationModule = "Project.ClobLimit.Spec";
const specificationClosure = specificationInputs(specificationModule);
const specificationPositions = new Map(
  specificationClosure.map((moduleName, index) => [moduleName, index]),
);
if (specificationPositions.has(specificationModule)) {
  throw new Error("behavioral specification input closure contains its root");
}
const specificationRoot = path.join(repoRoot, "proofs", "talos", "lean");
for (const [moduleName, index] of specificationPositions) {
  const source = path.join(
    specificationRoot,
    `${moduleName.replaceAll(".", path.sep)}.lean`,
  );
  for (const imported of leanImports(fs.readFileSync(source, "utf8"))) {
    const importedIndex = specificationPositions.get(imported);
    if (importedIndex !== undefined && importedIndex >= index) {
      throw new Error(`behavioral specification input order places ${imported} after ${moduleName}`);
    }
  }
}
for (const imported of leanImports(fs.readFileSync(path.join(
  specificationRoot,
  `${specificationModule.replaceAll(".", path.sep)}.lean`,
), "utf8"))) {
  if (!specificationPositions.has(imported)) {
    throw new Error(`behavioral specification input closure omits ${imported}`);
  }
}

const proofMutation = releaseInputs.files.map((file) => ({
  path: file.path,
  bytes: Buffer.from(file.sha256, "hex"),
}));
const beforeMutation = digestEntries(proofMutation);
const programIndex = proofMutation.findIndex((entry) => entry.path.endsWith("/Program.lean"));
proofMutation[programIndex].bytes[0] ^= 1;
if (digestEntries(proofMutation) === beforeMutation) {
  throw new Error("release identity ignored a cached Talos program mutation");
}

if (currentLocalDate(new Date(2026, 7, 2, 23, 59, 59)) !== "2026-08-02") {
  throw new Error("receipt dates do not use the machine's local calendar date");
}

process.stdout.write("checked verifier source membership and canonical input digests\n");
