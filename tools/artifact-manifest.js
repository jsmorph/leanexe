"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const { verifierSourceSha256 } = require("./artifact-source");

const manifestKeys = [
  "schemaVersion",
  "case",
  "sha256",
  "byteLength",
  "binaryFormatVersion",
  "validationProfile",
  "artifactBytesModule",
  "artifactBytesDefinition",
  "rawModuleDefinition",
  "cachedProgramModule",
  "cachedProgramDefinition",
  "specModule",
  "proofTarget",
  "identityTheorem",
  "decodeTheorem",
  "validationTheorem",
  "cacheEqualityTheorem",
  "artifactCorrectnessTheorem",
  "behaviorTheorems",
  "leanToolchain",
  "talosRevision",
  "verifierSourceSha256",
  "hostAssumptions",
];
const registryKeys = ["version", "artifacts"];
const entryKeys = ["case", "sha256", "manifest", "proofTarget"];
const leanName = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;

function fail(message) {
  throw new Error(message);
}

function exactKeys(value, expected, description) {
  if (value === null || typeof value !== "object" || Array.isArray(value)) {
    fail(`${description} must be an object`);
  }
  const found = Object.keys(value).sort();
  const wanted = [...expected].sort();
  if (found.length !== wanted.length || found.some((key, index) => key !== wanted[index])) {
    fail(`${description} must contain exactly: ${wanted.join(", ")}`);
  }
}

function readJson(file) {
  try {
    return JSON.parse(fs.readFileSync(file, "utf8"));
  } catch (error) {
    fail(`could not read ${file}: ${error.message}`);
  }
}

function sha256(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function requireLeanName(value, description) {
  if (typeof value !== "string" || !leanName.test(value)) {
    fail(`${description} must be a Lean declaration name`);
  }
}

function requireEqual(found, expected, description) {
  if (JSON.stringify(found) !== JSON.stringify(expected)) {
    fail(`${description} does not match the registered value`);
  }
}

function expectedTalosRevision(repoRoot) {
  const conformancePath = path.join(repoRoot, "proofs", "talos", "conformance.json");
  const conformance = readJson(conformancePath);
  if (!/^[0-9a-f]{40}$/.test(conformance.codeLibRevision)) {
    fail(`${conformancePath}: invalid codeLibRevision`);
  }
  const lakeManifestPath = path.join(
    repoRoot, "proofs", "talos", "lean", "lake-manifest.json",
  );
  const lakeManifest = readJson(lakeManifestPath);
  const codeLib = Array.isArray(lakeManifest.packages)
    ? lakeManifest.packages.find((item) => item.name === "CodeLib")
    : null;
  if (!codeLib || codeLib.type !== "git" || codeLib.rev !== conformance.codeLibRevision) {
    fail(`${lakeManifestPath}: CodeLib revision disagrees with conformance.json`);
  }
  return conformance.codeLibRevision;
}

function loadArtifactRegistry(repoRoot) {
  const artifactRoot = path.join(repoRoot, "proofs", "artifacts");
  const registryPath = path.join(artifactRoot, "registry.json");
  const registry = readJson(registryPath);
  exactKeys(registry, registryKeys, registryPath);
  if (registry.version !== 1 || !Array.isArray(registry.artifacts) ||
      registry.artifacts.length === 0) {
    fail(`${registryPath} has an unsupported schema`);
  }
  const seenCases = new Set();
  const seenDigests = new Set();
  const seenTargets = new Set();
  for (const [index, entry] of registry.artifacts.entries()) {
    const description = `${registryPath}: artifacts[${index}]`;
    exactKeys(entry, entryKeys, description);
    if (typeof entry.case !== "string" ||
        !/^[a-z][a-z0-9]*(?:_[a-z0-9]+)*$/.test(entry.case)) {
      fail(`${description}.case must be snake_case`);
    }
    if (!/^[0-9a-f]{64}$/.test(entry.sha256)) fail(`${description}: invalid SHA-256`);
    if (typeof entry.manifest !== "string" || path.isAbsolute(entry.manifest)) {
      fail(`${description}: invalid manifest path`);
    }
    requireLeanName(entry.proofTarget, `${description}.proofTarget`);
    if (seenCases.has(entry.case)) fail(`${registryPath}: duplicate case ${entry.case}`);
    if (seenDigests.has(entry.sha256)) fail(`${registryPath}: duplicate digest ${entry.sha256}`);
    if (seenTargets.has(entry.proofTarget)) {
      fail(`${registryPath}: duplicate proof target ${entry.proofTarget}`);
    }
    seenCases.add(entry.case);
    seenDigests.add(entry.sha256);
    seenTargets.add(entry.proofTarget);
  }
  return { artifactRoot, registryPath, registry };
}

function validateArtifactManifest(repoRoot, entry) {
  const artifactRoot = path.join(repoRoot, "proofs", "artifacts");
  const manifestPath = path.resolve(artifactRoot, entry.manifest);
  if (!manifestPath.startsWith(`${artifactRoot}${path.sep}`)) {
    fail(`manifest escapes the artifact root: ${entry.manifest}`);
  }
  const manifestStat = fs.lstatSync(manifestPath);
  if (!manifestStat.isFile() || manifestStat.isSymbolicLink()) {
    fail(`manifest is not a regular file: ${entry.manifest}`);
  }
  const manifest = readJson(manifestPath);
  exactKeys(manifest, manifestKeys, manifestPath);
  if (manifest.schemaVersion !== 3 || manifest.binaryFormatVersion !== 1 ||
      manifest.validationProfile !== "leanexe-core-v1") {
    fail(`${manifestPath} has an unsupported schema, binary format, or validation profile`);
  }
  for (const key of ["case", "sha256", "proofTarget"]) {
    if (manifest[key] !== entry[key]) fail(`${manifestPath}: ${key} disagrees with the registry`);
  }
  if (!/^[0-9a-f]{64}$/.test(manifest.sha256) ||
      path.basename(path.dirname(manifestPath)) !== manifest.sha256) {
    fail(`${manifestPath}: package path does not match its SHA-256`);
  }
  if (!Number.isSafeInteger(manifest.byteLength) || manifest.byteLength < 0) {
    fail(`${manifestPath}: invalid byteLength`);
  }
  for (const key of [
    "artifactBytesModule",
    "artifactBytesDefinition",
    "rawModuleDefinition",
    "cachedProgramModule",
    "cachedProgramDefinition",
    "specModule",
    "proofTarget",
    "identityTheorem",
    "decodeTheorem",
    "validationTheorem",
    "cacheEqualityTheorem",
    "artifactCorrectnessTheorem",
  ]) {
    requireLeanName(manifest[key], `${manifestPath}.${key}`);
  }
  if (!Array.isArray(manifest.behaviorTheorems) || manifest.behaviorTheorems.length === 0) {
    fail(`${manifestPath}: behaviorTheorems must be nonempty`);
  }
  const behaviorNames = new Set();
  for (const theorem of manifest.behaviorTheorems) {
    requireLeanName(theorem, `${manifestPath}.behaviorTheorems`);
    if (behaviorNames.has(theorem)) fail(`${manifestPath}: duplicate behavior theorem ${theorem}`);
    behaviorNames.add(theorem);
  }
  if (!Array.isArray(manifest.hostAssumptions) ||
      manifest.hostAssumptions.some((assumption) =>
        typeof assumption !== "string" || assumption.trim() !== assumption ||
        assumption.length === 0)) {
    fail(`${manifestPath}: hostAssumptions must contain trimmed, nonempty strings`);
  }
  if (new Set(manifest.hostAssumptions).size !== manifest.hostAssumptions.length) {
    fail(`${manifestPath}: hostAssumptions contains duplicates`);
  }

  const modulePrefix = manifest.proofTarget.replace(/\.ArtifactTranslation$/, "");
  const artifactNamespace = `${modulePrefix}.Artifact`;
  const expectedNames = {
    artifactBytesDefinition: `${artifactNamespace}.artifactBytes`,
    rawModuleDefinition: `${artifactNamespace}.Cache.raw`,
    cachedProgramDefinition: `${modulePrefix}.module`,
    identityTheorem: `${artifactNamespace}.decode_eq_cache`,
    cacheEqualityTheorem: `${artifactNamespace}.translation_cache_eq`,
    artifactCorrectnessTheorem: `${artifactNamespace}.artifact_module_eq_cache`,
  };
  if (modulePrefix === manifest.proofTarget) {
    fail(`${manifestPath}: proofTarget must end in .ArtifactTranslation`);
  }
  for (const [key, expected] of Object.entries(expectedNames)) {
    if (manifest[key] !== expected) fail(`${manifestPath}: ${key} must be ${expected}`);
  }
  if (manifest.artifactBytesModule !== `${modulePrefix}.ArtifactBytes` ||
      manifest.cachedProgramModule !== `${modulePrefix}.Program`) {
    fail(`${manifestPath}: artifact or cache module name disagrees with proofTarget`);
  }
  if (manifest.decodeTheorem !== "Wasm.Binary.Proof.decode_sound" ||
      manifest.validationTheorem !== "Wasm.Binary.Proof.validate_sound") {
    fail(`${manifestPath}: decoder and validator theorem names are unsupported`);
  }

  const casesPath = path.join(repoRoot, "proofs", "talos", "cases.json");
  const cases = readJson(casesPath);
  if (cases.version !== 1 || !Array.isArray(cases.cases)) {
    fail(`${casesPath} has an unsupported schema`);
  }
  const registeredCase = cases.cases.find((item) => item.name === manifest.case);
  if (!registeredCase) fail(`${manifestPath}: case is absent from cases.json`);
  requireEqual(manifest.specModule, registeredCase.specTarget, `${manifestPath}.specModule`);
  requireEqual(
    manifest.behaviorTheorems,
    registeredCase.behaviorTheorems,
    `${manifestPath}.behaviorTheorems`,
  );

  const rootToolchain = fs.readFileSync(path.join(repoRoot, "lean-toolchain"), "utf8").trim();
  const proofToolchain = fs.readFileSync(
    path.join(repoRoot, "proofs", "talos", "lean", "lean-toolchain"), "utf8",
  ).trim();
  if (rootToolchain !== proofToolchain || manifest.leanToolchain !== rootToolchain) {
    fail(`${manifestPath}: Lean toolchain disagrees with the workspace pins`);
  }
  if (manifest.talosRevision !== expectedTalosRevision(repoRoot)) {
    fail(`${manifestPath}: Talos revision disagrees with the proof workspace`);
  }
  if (manifest.verifierSourceSha256 !== verifierSourceSha256(repoRoot)) {
    fail(`${manifestPath}: verifier source identity mismatch`);
  }

  const binaryPath = path.join(path.dirname(manifestPath), "program.wasm");
  const binaryStat = fs.lstatSync(binaryPath);
  if (!binaryStat.isFile() || binaryStat.isSymbolicLink()) {
    fail(`${manifestPath}: frozen binary is not a regular file`);
  }
  const bytes = fs.readFileSync(binaryPath);
  if (sha256(bytes) !== manifest.sha256 || bytes.length !== manifest.byteLength) {
    fail(`${manifestPath}: frozen binary identity mismatch`);
  }
  return { manifest, manifestPath, binaryPath };
}

module.exports = {
  entryKeys,
  exactKeys,
  expectedTalosRevision,
  leanName,
  loadArtifactRegistry,
  manifestKeys,
  readJson,
  sha256,
  validateArtifactManifest,
};
