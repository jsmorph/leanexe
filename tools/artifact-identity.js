"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const {
  loadArtifactRegistry,
  sha256,
  validateArtifactManifest,
} = require("./artifact-manifest");
const { leanSourcesUnder, verifierSources } = require("./artifact-source");

const fixedInputs = [
  ".gitignore",
  ".node-version",
  ".wasm-tools-version",
  "lakefile.lean",
  "lake-manifest.json",
  "lean-toolchain",
  "proofs/talos/cases.json",
  "proofs/talos/conformance.json",
  "proofs/talos/lean/lakefile.toml",
  "proofs/talos/lean/lake-manifest.json",
  "proofs/talos/lean/lean-toolchain",
  "proofs/talos/lean/Project.lean",
  "proofs/artifacts/registry.json",
];

const verificationDriverInputs = [
  "tools/artifact-conformance.js",
  "tools/artifact-identity.js",
  "tools/artifact-manifest.js",
  "tools/artifact-proof.js",
  "tools/artifact-release.js",
  "tools/artifact-source.js",
  "tools/check-node-version.js",
  "tools/check-wasm-tools-version.sh",
  "tools/date.js",
  "tools/download-wasmtime.sh",
  "tools/leanrun",
  "tools/run-process.js",
];

const proofSourceRoots = ["proofs/talos/lean/Project"];
const directExecutables = [
  "tools/artifact-conformance.js",
  "tools/artifact-proof.js",
  "tools/artifact-release.js",
  "tools/check-wasm-tools-version.sh",
  "tools/download-wasmtime.sh",
  "tools/leanrun",
];

function localLeanImportClosure(repoRoot, initialPaths) {
  const found = new Set();
  const pending = [...initialPaths];
  while (pending.length > 0) {
    const relative = pending.pop();
    const source = fs.readFileSync(path.join(repoRoot, relative), "utf8");
    for (const line of source.split("\n")) {
      const code = line.split("--", 1)[0].trim();
      const match = /^import\s+(LeanExe(?:\.[A-Za-z_][A-Za-z0-9_]*)+)$/.exec(code);
      if (!match) continue;
      const imported = `${match[1].replaceAll(".", "/")}.lean`;
      if (found.has(imported)) continue;
      const stat = fs.lstatSync(path.join(repoRoot, imported));
      if (!stat.isFile() || stat.isSymbolicLink()) {
        throw new Error(`invalid local Lean import: ${imported}`);
      }
      found.add(imported);
      pending.push(imported);
    }
  }
  return [...found].sort(compareText);
}

function compareText(left, right) {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function readRegularFile(repoRoot, relative) {
  const absolute = path.join(repoRoot, ...relative.split("/"));
  const stat = fs.lstatSync(absolute);
  if (!stat.isFile() || stat.isSymbolicLink()) {
    throw new Error(`release input is not a regular file: ${relative}`);
  }
  return fs.readFileSync(absolute);
}

function digestEntries(entries) {
  const hash = crypto.createHash("sha256");
  hash.update("leanexe-release-input-v1\0");
  for (const entry of [...entries].sort((left, right) => compareText(left.path, right.path))) {
    hash.update(`${entry.path}\0${entry.bytes.length}\0`);
    hash.update(entry.bytes);
  }
  return hash.digest("hex");
}

function collectReleaseInputs(repoRoot) {
  const { registry } = loadArtifactRegistry(repoRoot);
  const paths = new Set([...fixedInputs, ...verificationDriverInputs]);
  const proofSources = leanSourcesUnder(repoRoot, proofSourceRoots);
  const cases = JSON.parse(fs.readFileSync(
    path.join(repoRoot, "proofs", "talos", "cases.json"),
    "utf8",
  ));
  if (cases.version !== 1 || !Array.isArray(cases.cases)) {
    throw new Error("proofs/talos/cases.json has an unsupported schema");
  }
  const expectedPrograms = cases.cases.map((item) =>
    `proofs/talos/lean/Project/${item.leanModule}/Program.lean`).sort(compareText);
  const foundPrograms = proofSources.map((source) => source.relative)
    .filter((relative) => relative.endsWith("/Program.lean"))
    .sort(compareText);
  if (JSON.stringify(foundPrograms) !== JSON.stringify(expectedPrograms)) {
    throw new Error("tracked Talos program caches do not match cases.json");
  }
  for (const source of proofSources) {
    paths.add(source.relative);
  }
  for (const relative of localLeanImportClosure(repoRoot, [
    "proofs/talos/lean/Project.lean",
    ...proofSources.map((source) => source.relative),
  ])) paths.add(relative);
  for (const source of verifierSources(repoRoot)) paths.add(source.relative);
  for (const entry of registry.artifacts) {
    const { manifestPath, binaryPath } = validateArtifactManifest(repoRoot, entry);
    paths.add(path.relative(repoRoot, manifestPath).split(path.sep).join("/"));
    paths.add(path.relative(repoRoot, binaryPath).split(path.sep).join("/"));
  }
  for (const relative of directExecutables) {
    const stat = fs.lstatSync(path.join(repoRoot, relative));
    if (!stat.isFile() || stat.isSymbolicLink() || (stat.mode & 0o111) === 0) {
      throw new Error(`release driver is not an executable regular file: ${relative}`);
    }
  }
  const entries = [...paths].sort(compareText).map((relative) => {
    const bytes = readRegularFile(repoRoot, relative);
    return {
      path: relative,
      byteLength: bytes.length,
      sha256: sha256(bytes),
      bytes,
    };
  });
  return {
    schemaVersion: 1,
    sha256: digestEntries(entries),
    files: entries.map(({ path: relative, byteLength, sha256: fileDigest }) => ({
      path: relative,
      byteLength,
      sha256: fileDigest,
    })),
  };
}

function compareReleaseInputs(expected, found) {
  if (expected.sha256 === found.sha256) return;
  const expectedByPath = new Map(expected.files.map((file) => [file.path, file]));
  const foundByPath = new Map(found.files.map((file) => [file.path, file]));
  const differences = [];
  for (const relative of [...new Set([...expectedByPath.keys(), ...foundByPath.keys()])]
    .sort(compareText)) {
    const left = expectedByPath.get(relative);
    const right = foundByPath.get(relative);
    if (!left) differences.push(`${relative}: absent from expected inputs`);
    else if (!right) differences.push(`${relative}: absent from found inputs`);
    else if (left.sha256 !== right.sha256 || left.byteLength !== right.byteLength) {
      differences.push(`${relative}: content differs`);
    }
  }
  throw new Error(`release inputs differ:\n${differences.join("\n")}`);
}

module.exports = {
  collectReleaseInputs,
  compareReleaseInputs,
  directExecutables,
  digestEntries,
  fixedInputs,
  localLeanImportClosure,
  proofSourceRoots,
  verificationDriverInputs,
};
