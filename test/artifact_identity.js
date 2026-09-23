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
  localModuleInputs,
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
const expectedVerifierDigest = "0b8486bea82c65a31ecdf332642f8d96fcf99f2726130f56707f373c02017194";
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
const programSources = proofSources
  .map((source) => source.relative)
  .filter((source) => source.endsWith("/Program.lean"))
  .sort();
const registeredPrograms = JSON.parse(fs.readFileSync(
  path.join(repoRoot, "proofs/talos/cases.json"), "utf8",
)).cases.map((item) => `proofs/talos/lean/Project/${item.leanModule}/Program.lean`).sort();
if (JSON.stringify(programSources) !== JSON.stringify(registeredPrograms)) {
  throw new Error("release identity's cached Talos programs differ from the case registry");
}
const localImports = localLeanImportClosure(repoRoot, [
  "proofs/talos/lean/Project.lean",
  ...proofSources.map((source) => source.relative),
]);
const expectedLocalImports = [
  "LeanExe/Examples/AsciiDigits.lean",
  "LeanExe/Examples/EulerRiemann/Grid.lean",
  "LeanExe/Examples/Packed.lean",
  "LeanExe/Examples/TalosAssocList.lean",
  "LeanExe/Float32.lean",
  "LeanExe/Models/Gpt2/Block.lean",
  "LeanExe/Models/Gpt2/Cached.lean",
  "LeanExe/Models/Gpt2/Inference.lean",
  "LeanExe/Models/Gpt2/Kernel.lean",
  "LeanExe/Models/Gpt2/Numerics.lean",
  "LeanExe/Models/Gpt2/Quantized/Cached.lean",
  "LeanExe/Models/Gpt2/Quantized/Format.lean",
  "LeanExe/Models/Gpt2/Quantized/Grouped.lean",
  "LeanExe/Models/Gpt2/Quantized/Kernel.lean",
  "LeanExe/Packed.lean",
  "LeanExe/Runtime.lean",
  "LeanExe/Signed32.lean",
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

const specificationRoot = path.join(repoRoot, "proofs", "talos", "lean");
for (const rootModule of [
  "Project.ClobLimit.Spec",
  "Project.Gpt2CachedStep.ArtifactTranslation",
  "Project.EulerReconstructed.ArtifactDecoded",
]) {
  const positions = new Map(
    localModuleInputs(rootModule).map((moduleName, index) => [moduleName, index]),
  );
  if (positions.has(rootModule)) {
    throw new Error(`local input closure contains its root ${rootModule}`);
  }
  for (const [moduleName, index] of [...positions, [rootModule, positions.size]]) {
    const source = path.join(specificationRoot, `${moduleName.replaceAll(".", path.sep)}.lean`);
    for (const imported of leanImports(fs.readFileSync(source, "utf8"))) {
      const importedSource = path.join(specificationRoot, `${imported.replaceAll(".", path.sep)}.lean`);
      if (!fs.existsSync(importedSource)) continue;
      const importedIndex = positions.get(imported);
      if (importedIndex === undefined) throw new Error(`local input closure omits ${imported}`);
      if (importedIndex >= index) {
        throw new Error(`local input order places ${imported} after ${moduleName}`);
      }
    }
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
