#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { loadArtifactRegistry, validateArtifactManifest } = require("../tools/artifact-manifest");
const { verifierSources } = require("../tools/artifact-source");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

const repoRoot = path.resolve(__dirname, "..");
const { registry } = loadArtifactRegistry(repoRoot);
const entry = registry.artifacts.find((item) => item.case === "gcd");
assert.ok(entry, "GCD artifact is absent");
const original = validateArtifactManifest(repoRoot, entry).manifest;
const root = makeTemporaryDirectory("leanexe-manifest-test-");
try {
  const manifestRelative = path.join("proofs/artifacts", entry.manifest);
  const files = [
    "lean-toolchain",
    "proofs/talos/lean/lean-toolchain",
    "proofs/talos/lean/lake-manifest.json",
    "proofs/talos/conformance.json",
    "proofs/talos/cases.json",
    manifestRelative,
    path.join(path.dirname(manifestRelative), "program.wasm"),
    ...verifierSources(repoRoot).map((source) => source.relative),
  ];
  for (const relative of files) {
    const destination = path.join(root, relative);
    fs.mkdirSync(path.dirname(destination), { recursive: true });
    fs.copyFileSync(path.join(repoRoot, relative), destination);
  }
  const manifestPath = path.join(root, manifestRelative);
  function check(manifest) {
    fs.writeFileSync(manifestPath, JSON.stringify(manifest));
    return validateArtifactManifest(root, entry);
  }
  const current = {
    ...original,
    cachedProgramModule: "Project.Gcd.Program",
    cachedProgramDefinition: "Project.Gcd.module",
    specModule: "Project.Gcd.Spec",
    behaviorTheorems: ["Project.Gcd.Spec.gcd_correct"],
  };
  const frozen = {
    ...original,
    cachedProgramModule: "Project.Gcd.FrozenProgram",
    cachedProgramDefinition: "Project.Gcd.Frozen.module",
    specModule: "Project.Gcd.FrozenSpec",
    behaviorTheorems: ["Project.Gcd.Frozen.Spec.gcd_correct"],
  };
  check(current);
  check(frozen);
  assert.throws(() => check({ ...frozen, cachedProgramDefinition: current.cachedProgramDefinition }),
    /cachedProgramDefinition must be/);
  assert.throws(() => check({ ...frozen, specModule: current.specModule }),
    /specModule does not match/);
  assert.throws(() => check({ ...frozen, behaviorTheorems: current.behaviorTheorems }),
    /behaviorTheorems does not match/);
  assert.throws(() => check({ ...current, cachedProgramModule: "Project.Gcd.UnrelatedProgram" }),
    /cache module name disagrees/);
  assert.throws(() => check({ ...frozen, behaviorTheorems: ["Project.Gcd.Frozen.Spec.unrelated"] }),
    /behaviorTheorems does not match/);
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}

process.stdout.write("checked current and frozen artifact manifest bindings\n");
