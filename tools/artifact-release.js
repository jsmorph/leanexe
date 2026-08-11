#!/usr/bin/env node
"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const { runCheckedAsync, spawnResultAsync } = require("./run-process");
const { collectReleaseInputs, compareReleaseInputs } = require("./artifact-identity");
const {
  loadArtifactRegistry,
  validateArtifactManifest,
} = require("./artifact-manifest");
const { currentLocalDate } = require("./date");
const { leanSourcesUnder } = require("./artifact-source");
const { makeTemporaryDirectory } = require("./temp-directory");

const repoRoot = path.resolve(__dirname, "..");
const artifactRoot = path.join(repoRoot, "proofs", "artifacts");
const evidencePath = path.join(artifactRoot, "release.json");
const registryPath = path.join(artifactRoot, "registry.json");
const conformancePath = path.join(repoRoot, "proofs", "talos", "conformance.json");
const receiptRoot = path.join(repoRoot, "build", "evidence");

const topKeys = [
  "schemaVersion",
  "status",
  "recordedDate",
  "sourceRevision",
  "releaseInputSha256",
  "artifactRegistry",
  "packages",
  "tools",
  "kernelReview",
  "artifactProof",
  "semanticConformance",
  "coldCheckout",
  "blockers",
];
const packageKeys = [
  "case",
  "sha256",
  "manifestSha256",
  "proofTarget",
  "identityTheorem",
  "decodeTheorem",
  "validationTheorem",
  "cacheEqualityTheorem",
  "artifactCorrectnessTheorem",
  "behaviorTheorems",
];

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

function fileSha256(file) {
  return sha256(fs.readFileSync(file));
}

function writeJsonAtomic(file, value) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  const temporary = `${file}.tmp-${process.pid}`;
  fs.writeFileSync(temporary, `${JSON.stringify(value, null, 2)}\n`);
  fs.renameSync(temporary, file);
}

function optionalJson(file) {
  try {
    return readJson(file);
  } catch (error) {
    if (error.message.includes("ENOENT")) return null;
    throw error;
  }
}

function requireEqual(found, expected, description) {
  if (JSON.stringify(found) !== JSON.stringify(expected)) {
    fail(`${description} does not match the recorded input`);
  }
}

function derivedBlockers(evidence) {
  const blockers = [];
  if (evidence.sourceRevision === null) {
    blockers.push("No immutable source revision records the current proof implementation.");
  }
  if (!["reproduction-rejected", "affected-accepted-after-source-audit"].includes(
    evidence.kernelReview.selectedResult,
  )) {
    blockers.push("The proof kernel has no accepted disposition for the recorded defect.");
  }
  if (evidence.artifactProof.result !== "passed") {
    blockers.push("The aggregate artifact proof has not passed under the selected toolchain.");
  }
  if (!["passed", "passed-with-warning"].includes(evidence.semanticConformance.result)) {
    blockers.push("The conformance gate has not passed under the selected toolchain.");
  }
  if (evidence.coldCheckout.status !== "passed") {
    blockers.push("The release gates have not passed from a cold checkout of the recorded source revision.");
  }
  return blockers;
}

function receiptMatches(receipt, expectedKeys, predicates) {
  if (receipt === null || typeof receipt !== "object" || Array.isArray(receipt)) return false;
  const found = Object.keys(receipt).sort();
  const wanted = [...expectedKeys].sort();
  if (found.length !== wanted.length || found.some((key, index) => key !== wanted[index])) {
    return false;
  }
  return predicates.every((predicate) => predicate(receipt));
}

function refreshEvidence() {
  const previous = readJson(evidencePath);
  const inputs = collectReleaseInputs(repoRoot);
  const { registry } = loadArtifactRegistry(repoRoot);
  const conformance = readJson(conformancePath);
  const packages = registry.artifacts.map((entry) => {
    const { manifest, manifestPath } = validateArtifactManifest(repoRoot, entry);
    return {
      case: entry.case,
      sha256: entry.sha256,
      manifestSha256: fileSha256(manifestPath),
      proofTarget: manifest.proofTarget,
      identityTheorem: manifest.identityTheorem,
      decodeTheorem: manifest.decodeTheorem,
      validationTheorem: manifest.validationTheorem,
      cacheEqualityTheorem: manifest.cacheEqualityTheorem,
      artifactCorrectnessTheorem: manifest.artifactCorrectnessTheorem,
      behaviorTheorems: manifest.behaviorTheorems,
    };
  });
  const sourceRevision = previous.releaseInputSha256 === inputs.sha256
    ? previous.sourceRevision
    : null;

  const artifactReceipt = optionalJson(path.join(receiptRoot, "artifact-proof.json"));
  const artifactPassed = receiptMatches(artifactReceipt,
    ["schemaVersion", "date", "result", "artifactCount", "releaseInputSha256"], [
      (receipt) => receipt.schemaVersion === 1 && receipt.result === "passed",
      (receipt) => /^\d{4}-\d{2}-\d{2}$/.test(receipt.date),
      (receipt) => receipt.artifactCount === registry.artifacts.length,
      (receipt) => receipt.releaseInputSha256 === inputs.sha256,
    ]);

  const conformanceReceipt = optionalJson(path.join(receiptRoot, "artifact-conformance.json"));
  const conformancePassed = receiptMatches(conformanceReceipt, [
    "schemaVersion",
    "date",
    "result",
    "configSha256",
    "releaseInputSha256",
    "officialFileCount",
    "officialValidatorCases",
    "talos",
    "wasmtimeFilesPassed",
    "warnings",
  ], [
    (receipt) => receipt.schemaVersion === 1,
    (receipt) => /^\d{4}-\d{2}-\d{2}$/.test(receipt.date),
    (receipt) => ["passed", "passed-with-warning"].includes(receipt.result),
    (receipt) => receipt.configSha256 === fileSha256(conformancePath),
    (receipt) => receipt.releaseInputSha256 === inputs.sha256,
  ]);

  const coldReceipt = optionalJson(path.join(receiptRoot, "cold-checkout.json"));
  const coldConformanceResult = conformance.knownIssues.length === 0
    ? "passed"
    : "passed-with-warning";
  const coldPassed = sourceRevision !== null && receiptMatches(coldReceipt, [
    "schemaVersion",
    "sourceRevision",
    "releaseInputSha256",
    "date",
    "artifactProof",
    "semanticConformance",
  ], [
    (receipt) => receipt.schemaVersion === 1,
    (receipt) => receipt.sourceRevision === sourceRevision,
    (receipt) => receipt.releaseInputSha256 === inputs.sha256,
    (receipt) => /^\d{4}-\d{2}-\d{2}$/.test(receipt.date),
    (receipt) => receipt.artifactProof === "passed",
    (receipt) => receipt.semanticConformance === coldConformanceResult,
  ]);

  const next = {
    schemaVersion: 2,
    status: "draft",
    recordedDate: currentLocalDate(),
    sourceRevision,
    releaseInputSha256: inputs.sha256,
    artifactRegistry: {
      path: "proofs/artifacts/registry.json",
      sha256: fileSha256(registryPath),
      artifactCount: registry.artifacts.length,
    },
    packages,
    tools: {
      node: fs.readFileSync(path.join(repoRoot, ".node-version"), "utf8").trim(),
      wasmTools: fs.readFileSync(path.join(repoRoot, ".wasm-tools-version"), "utf8").trim(),
      lean: fs.readFileSync(path.join(repoRoot, "lean-toolchain"), "utf8").trim(),
      talosRevision: conformance.codeLibRevision,
      testsuiteRevision: conformance.testsuiteRevision,
      wasmtime: conformance.wasmtimeVersion,
    },
    kernelReview: previous.kernelReview,
    artifactProof: artifactPassed ? {
      command: "tools/artifact-proof.js check-all",
      date: artifactReceipt.date,
      result: "passed",
      artifactCount: artifactReceipt.artifactCount,
      releaseInputSha256: inputs.sha256,
    } : {
      command: "tools/artifact-proof.js check-all",
      date: null,
      result: "pending",
      artifactCount: registry.artifacts.length,
      releaseInputSha256: null,
    },
    semanticConformance: conformancePassed ? {
      command: "tools/artifact-conformance.js check",
      configSha256: conformanceReceipt.configSha256,
      releaseInputSha256: inputs.sha256,
      date: conformanceReceipt.date,
      result: conformanceReceipt.result,
      officialFileCount: conformanceReceipt.officialFileCount,
      officialValidatorCases: conformanceReceipt.officialValidatorCases,
      talos: conformanceReceipt.talos,
      wasmtimeFilesPassed: conformanceReceipt.wasmtimeFilesPassed,
      warnings: conformanceReceipt.warnings,
    } : {
      command: "tools/artifact-conformance.js check",
      configSha256: fileSha256(conformancePath),
      releaseInputSha256: null,
      date: null,
      result: "pending",
      officialFileCount: conformance.files.length,
      officialValidatorCases: conformance.validatorCases.length,
      talos: {
        pass: 0,
        fail: 0,
        skip: 0,
        cascade: 0,
        decodeError: 0,
        interpreterError: 0,
        outOfFuel: 0,
      },
      wasmtimeFilesPassed: 0,
      warnings: [],
    },
    coldCheckout: {
      status: coldPassed ? "passed" : "pending",
      sourceRevision,
      releaseInputSha256: coldPassed ? inputs.sha256 : null,
      date: coldPassed ? coldReceipt.date : null,
      command: "tools/artifact-release.js check-cold <revision>",
    },
    blockers: [],
  };
  next.blockers = derivedBlockers(next);
  next.status = next.blockers.length === 0 ? "ready" : "draft";
  writeJsonAtomic(evidencePath, next);
  return next;
}

function kernelScopeFindings(repoRoot, scopeAudit) {
  const findings = [];
  const sources = leanSourcesUnder(repoRoot, scopeAudit.roots);
  for (const relative of scopeAudit.sources) {
    const absolute = path.join(repoRoot, relative);
    const stat = fs.lstatSync(absolute);
    if (!stat.isFile() || stat.isSymbolicLink()) {
      fail(`kernel scope source is not a regular file: ${relative}`);
    }
    sources.push({ absolute, relative });
  }
  sources.sort((left, right) => left.relative < right.relative ? -1 :
    left.relative > right.relative ? 1 : 0);
  for (const source of sources) {
    const lines = fs.readFileSync(source.absolute, "utf8").split("\n");
    for (const [index, line] of lines.entries()) {
      for (const identifier of scopeAudit.forbiddenIdentifiers) {
        const pattern = new RegExp(`\\b${identifier}\\b`);
        if (pattern.test(line)) {
          findings.push(`${source.relative}:${index + 1}: ${identifier}`);
        }
      }
    }
  }
  return findings;
}

function validateEvidence(evidence) {
  exactKeys(evidence, topKeys, evidencePath);
  if (evidence.schemaVersion !== 2 || !["draft", "ready"].includes(evidence.status)) {
    fail(`${evidencePath} has an unsupported schema or status`);
  }
  if (!/^\d{4}-\d{2}-\d{2}$/.test(evidence.recordedDate)) {
    fail(`${evidencePath}: invalid recordedDate`);
  }
  if (evidence.sourceRevision !== null && !/^[0-9a-f]{40}$/.test(evidence.sourceRevision)) {
    fail(`${evidencePath}: invalid sourceRevision`);
  }

  const releaseInputs = collectReleaseInputs(repoRoot);
  if (evidence.releaseInputSha256 !== releaseInputs.sha256) {
    fail(`${evidencePath}: release input identity mismatch`);
  }

  exactKeys(evidence.artifactRegistry, ["path", "sha256", "artifactCount"],
    `${evidencePath}: artifactRegistry`);
  if (evidence.artifactRegistry.path !== "proofs/artifacts/registry.json" ||
      evidence.artifactRegistry.sha256 !== fileSha256(registryPath)) {
    fail(`${evidencePath}: artifact registry identity mismatch`);
  }
  const registry = loadArtifactRegistry(repoRoot).registry;
  if (registry.version !== 1 || !Array.isArray(registry.artifacts) ||
      evidence.artifactRegistry.artifactCount !== registry.artifacts.length) {
    fail(`${evidencePath}: artifact registry count mismatch`);
  }
  if (!Array.isArray(evidence.packages) || evidence.packages.length !== registry.artifacts.length) {
    fail(`${evidencePath}: packages must record every registry entry`);
  }
  for (const [index, recorded] of evidence.packages.entries()) {
    exactKeys(recorded, packageKeys, `${evidencePath}: packages[${index}]`);
    const entry = registry.artifacts[index];
    if (recorded.case !== entry.case || recorded.sha256 !== entry.sha256 ||
        recorded.proofTarget !== entry.proofTarget) {
      fail(`${evidencePath}: packages[${index}] disagrees with the artifact registry`);
    }
    const manifestPath = path.resolve(artifactRoot, entry.manifest);
    if (!manifestPath.startsWith(`${artifactRoot}${path.sep}`) ||
        recorded.manifestSha256 !== fileSha256(manifestPath)) {
      fail(`${evidencePath}: ${recorded.case} manifest identity mismatch`);
    }
    const { manifest } = validateArtifactManifest(repoRoot, entry);
    for (const key of [
      "proofTarget",
      "identityTheorem",
      "decodeTheorem",
      "validationTheorem",
      "cacheEqualityTheorem",
      "artifactCorrectnessTheorem",
      "behaviorTheorems",
    ]) {
      requireEqual(recorded[key], manifest[key], `${recorded.case} ${key}`);
    }
    const binaryPath = path.join(path.dirname(manifestPath), "program.wasm");
    if (fileSha256(binaryPath) !== recorded.sha256) {
      fail(`${evidencePath}: ${recorded.case} binary identity mismatch`);
    }
  }

  exactKeys(evidence.tools, [
    "node",
    "wasmTools",
    "lean",
    "talosRevision",
    "testsuiteRevision",
    "wasmtime",
  ], `${evidencePath}: tools`);
  const conformance = readJson(conformancePath);
  requireEqual(evidence.tools.node,
    fs.readFileSync(path.join(repoRoot, ".node-version"), "utf8").trim(), "Node pin");
  requireEqual(evidence.tools.wasmTools,
    fs.readFileSync(path.join(repoRoot, ".wasm-tools-version"), "utf8").trim(),
    "wasm-tools pin");
  const rootLean = fs.readFileSync(path.join(repoRoot, "lean-toolchain"), "utf8").trim();
  const proofLean = fs.readFileSync(
    path.join(repoRoot, "proofs", "talos", "lean", "lean-toolchain"), "utf8").trim();
  requireEqual(rootLean, proofLean, "Lean workspace pins");
  requireEqual(evidence.tools.lean, rootLean, "Lean release pin");
  requireEqual(evidence.tools.talosRevision, conformance.codeLibRevision, "Talos pin");
  requireEqual(evidence.tools.testsuiteRevision, conformance.testsuiteRevision,
    "WebAssembly testsuite pin");
  requireEqual(evidence.tools.wasmtime, conformance.wasmtimeVersion, "Wasmtime pin");

  exactKeys(evidence.kernelReview, [
    "selectedToolchain",
    "selectedResult",
    "candidateToolchain",
    "candidateCommit",
    "candidateResult",
    "scopeAudit",
    "reproductionSource",
    "reproductionSha256",
  ], `${evidencePath}: kernelReview`);
  requireEqual(evidence.kernelReview.selectedToolchain, evidence.tools.lean,
    "selected kernel toolchain");
  if (!["affected", "reproduction-rejected", "affected-accepted-after-source-audit"].includes(
        evidence.kernelReview.selectedResult) ||
      !/^[0-9a-f]{40}$/.test(evidence.kernelReview.candidateCommit) ||
      !["reproduction-accepted", "reproduction-rejected"].includes(
        evidence.kernelReview.candidateResult) ||
      !/^[0-9a-f]{64}$/.test(evidence.kernelReview.reproductionSha256)) {
    fail(`${evidencePath}: invalid kernel review`);
  }
  exactKeys(evidence.kernelReview.scopeAudit, [
    "command",
    "date",
    "result",
    "roots",
    "sources",
    "forbiddenIdentifiers",
  ], `${evidencePath}: kernelReview.scopeAudit`);
  const scopeAudit = evidence.kernelReview.scopeAudit;
  requireEqual(scopeAudit.command, "tools/artifact-release.js audit-kernel-scope",
    "kernel scope audit command");
  requireEqual(scopeAudit.roots, ["proofs/talos/lean/Project"],
    "kernel scope audit roots");
  requireEqual(scopeAudit.sources, [
    "LeanExe/Examples/AsciiDigits.lean",
    "LeanExe/Examples/TalosAssocList.lean",
  ], "kernel scope audit sources");
  requireEqual(scopeAudit.forbiddenIdentifiers, ["addDecl", "inductDecl"],
    "kernel scope audit identifiers");
  if (!/^\d{4}-\d{2}-\d{2}$/.test(scopeAudit.date) || scopeAudit.result !== "passed") {
    fail(`${evidencePath}: invalid kernel scope audit result`);
  }
  const scopeFindings = kernelScopeFindings(repoRoot, scopeAudit);
  if (scopeFindings.length > 0) {
    fail(`kernel scope audit found forbidden identifiers:\n${scopeFindings.join("\n")}`);
  }
  if (evidence.kernelReview.selectedResult === "affected-accepted-after-source-audit" &&
      (evidence.kernelReview.selectedToolchain !== evidence.kernelReview.candidateToolchain ||
       evidence.kernelReview.candidateResult !== "reproduction-accepted")) {
    fail(`${evidencePath}: audited affected toolchain does not match the accepted reproduction`);
  }
  if (evidence.kernelReview.selectedResult === "reproduction-rejected" &&
      (evidence.kernelReview.selectedToolchain !== evidence.kernelReview.candidateToolchain ||
       evidence.kernelReview.candidateResult !== "reproduction-rejected")) {
    fail(`${evidencePath}: selected fixed kernel does not match the rejected reproduction`);
  }

  exactKeys(evidence.artifactProof,
    ["command", "date", "result", "artifactCount", "releaseInputSha256"],
    `${evidencePath}: artifactProof`);
  if (evidence.artifactProof.command !== "tools/artifact-proof.js check-all" ||
      !["pending", "passed"].includes(evidence.artifactProof.result) ||
      evidence.artifactProof.artifactCount !== registry.artifacts.length) {
    fail(`${evidencePath}: invalid artifact proof result`);
  }
  if ((evidence.artifactProof.result === "passed") !==
      /^\d{4}-\d{2}-\d{2}$/.test(evidence.artifactProof.date || "")) {
    fail(`${evidencePath}: artifact proof date disagrees with its result`);
  }
  requireEqual(
    evidence.artifactProof.releaseInputSha256,
    evidence.artifactProof.result === "pending" ? null : evidence.releaseInputSha256,
    "artifact proof release input identity",
  );
  exactKeys(evidence.semanticConformance, [
    "command",
    "configSha256",
    "releaseInputSha256",
    "date",
    "result",
    "officialFileCount",
    "officialValidatorCases",
    "talos",
    "wasmtimeFilesPassed",
    "warnings",
  ], `${evidencePath}: semanticConformance`);
  exactKeys(evidence.semanticConformance.talos,
    ["pass", "fail", "skip", "cascade", "decodeError", "interpreterError", "outOfFuel"],
    `${evidencePath}: semanticConformance.talos`);
  const warningIds = conformance.knownIssues.map((issue) => issue.id);
  const configuredFailures = conformance.knownIssues.reduce(
    (total, issue) => total + issue.failures.length, 0);
  const talos = evidence.semanticConformance.talos;
  for (const [name, value] of Object.entries(talos)) {
    if (!Number.isSafeInteger(value) || value < 0) {
      fail(`${evidencePath}: invalid Talos ${name} count`);
    }
  }
  const expectedConformanceResult = warningIds.length > 0 ? "passed-with-warning" : "passed";
  if (evidence.semanticConformance.command !== "tools/artifact-conformance.js check" ||
      evidence.semanticConformance.configSha256 !== fileSha256(conformancePath) ||
      !["pending", "passed", "passed-with-warning"].includes(
        evidence.semanticConformance.result) ||
      evidence.semanticConformance.officialFileCount !== conformance.files.length ||
      evidence.semanticConformance.officialValidatorCases !== conformance.validatorCases.length ||
      (evidence.semanticConformance.result === "pending" && (
        Object.values(evidence.semanticConformance.talos).some((value) => value !== 0) ||
        evidence.semanticConformance.wasmtimeFilesPassed !== 0 ||
        evidence.semanticConformance.warnings.length !== 0 ||
        evidence.semanticConformance.date !== null
      )) ||
      (evidence.semanticConformance.result !== "pending" && (
        !/^\d{4}-\d{2}-\d{2}$/.test(evidence.semanticConformance.date || "") ||
        evidence.semanticConformance.result !== expectedConformanceResult ||
        talos.fail !== configuredFailures ||
        talos.cascade !== 0 ||
        talos.decodeError !== 0 ||
        talos.interpreterError !== 0 ||
        talos.outOfFuel !== 0 ||
        evidence.semanticConformance.wasmtimeFilesPassed !== conformance.files.length
      ))) {
    fail(`${evidencePath}: semantic conformance result disagrees with its configuration`);
  }
  requireEqual(evidence.semanticConformance.warnings,
    evidence.semanticConformance.result === "pending" ? [] : warningIds,
    "semantic conformance warnings");
  requireEqual(
    evidence.semanticConformance.releaseInputSha256,
    evidence.semanticConformance.result === "pending" ? null : evidence.releaseInputSha256,
    "semantic conformance release input identity",
  );

  exactKeys(evidence.coldCheckout,
    ["status", "sourceRevision", "releaseInputSha256", "date", "command"],
    `${evidencePath}: coldCheckout`);
  if (!["pending", "passed"].includes(evidence.coldCheckout.status) ||
      evidence.coldCheckout.sourceRevision !== evidence.sourceRevision ||
      evidence.coldCheckout.releaseInputSha256 !==
        (evidence.coldCheckout.status === "pending" ? null : evidence.releaseInputSha256) ||
      ((evidence.coldCheckout.status === "passed") !==
        /^\d{4}-\d{2}-\d{2}$/.test(evidence.coldCheckout.date || "")) ||
      evidence.coldCheckout.command !== "tools/artifact-release.js check-cold <revision>") {
    fail(`${evidencePath}: invalid cold-checkout record`);
  }
  const blockers = derivedBlockers(evidence);
  requireEqual(evidence.blockers, blockers, "release blockers");
  if ((evidence.status === "ready") !== (blockers.length === 0)) {
    fail(`${evidencePath}: status does not agree with the release blockers`);
  }
  return blockers;
}

function loadEvidence() {
  const evidence = readJson(evidencePath);
  const blockers = validateEvidence(evidence);
  return { evidence, blockers };
}

async function run(args, options = {}) {
  await runCheckedAsync(args, {
    cwd: options.cwd || repoRoot,
    env: options.env || process.env,
    stdio: "inherit",
  });
}

async function requireCleanCheckout(root, stage) {
  const result = await spawnResultAsync([
    "git", "status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none",
  ], { cwd: root });
  if (result.status !== 0) fail(`could not inspect the cold checkout ${stage}`);
  const output = result.stdout.toString("utf8").trim();
  if (output !== "") fail(`cold checkout changed ${stage}:\n${output}`);
}

async function requireRevision(root, expected, description) {
  const result = await spawnResultAsync(["git", "rev-parse", "HEAD"], { cwd: root });
  const found = result.stdout.toString("utf8").trim();
  if (result.status !== 0 || found !== expected) {
    fail(`${description} revision mismatch: expected ${expected}, found ${found || "unavailable"}`);
  }
  const status = await spawnResultAsync([
    "git", "status", "--porcelain=v1", "--untracked-files=no", "--ignore-submodules=none",
  ], { cwd: root });
  const changes = status.stdout.toString("utf8").trim();
  if (status.status !== 0 || changes !== "") {
    fail(`${description} checkout is not clean${changes ? `:\n${changes}` : ""}`);
  }
}

async function checkSelectedLean(checkout, evidence) {
  const result = await spawnResultAsync([
    path.join(checkout, "tools", "leanrun"), "--timeout", "2m", "lean", "--version",
  ], { cwd: checkout });
  const output = `${result.stdout.toString("utf8")}\n${result.stderr.toString("utf8")}`.trim();
  const version = evidence.kernelReview.selectedToolchain.split(":v")[1];
  if (result.status !== 0 || !output.includes(`version ${version}`) ||
      !output.includes(`commit ${evidence.kernelReview.candidateCommit}`)) {
    fail(`cold Lean identity mismatch: ${output}`);
  }
}

async function checkDependencyRevisions(checkout, evidence) {
  const codeLib = path.join(checkout, "proofs", "talos", "lean", ".lake", "packages", "CodeLib");
  const testsuite = path.join(codeLib, "vendor", "testsuite");
  await requireRevision(codeLib, evidence.tools.talosRevision, "CodeLib");
  await requireRevision(testsuite, evidence.tools.testsuiteRevision, "WebAssembly testsuite");
}

async function checkCold(revision, evidence) {
  if (!/^[0-9a-f]{40}$/.test(revision) || evidence.sourceRevision !== revision) {
    fail("the cold-checkout revision must equal the release sourceRevision");
  }
  if (!["reproduction-rejected", "affected-accepted-after-source-audit"].includes(
    evidence.kernelReview.selectedResult,
  )) {
    fail("the selected Lean toolchain has no accepted kernel-defect disposition");
  }
  const temporaryRoot = makeTemporaryDirectory("leanexe-release-");
  const checkout = path.join(temporaryRoot, "source");
  const expectedInputs = collectReleaseInputs(repoRoot);
  try {
    await run(["git", "clone", "--no-local", "--quiet", repoRoot, checkout]);
    await run(["git", "checkout", "--detach", revision], { cwd: checkout });
    const foundInputs = collectReleaseInputs(checkout);
    compareReleaseInputs(expectedInputs, foundInputs);
    const coldScopeFindings = kernelScopeFindings(checkout, evidence.kernelReview.scopeAudit);
    if (coldScopeFindings.length > 0) {
      fail(`cold kernel scope audit found forbidden identifiers:\n${coldScopeFindings.join("\n")}`);
    }
    const head = await spawnResultAsync(["git", "rev-parse", "HEAD"], { cwd: checkout });
    if (head.status !== 0 || head.stdout.toString("utf8").trim() !== revision) {
      fail("cold checkout did not select the recorded source revision");
    }
    await requireCleanCheckout(checkout, "before dependency setup");
    await run([process.execPath, "tools/check-node-version.js"], { cwd: checkout });
    await run(["tools/check-wasm-tools-version.sh"], { cwd: checkout });
    await run(["tools/download-wasmtime.sh"], { cwd: checkout });
    await checkSelectedLean(checkout, evidence);
    await run([
      "tools/leanrun", "--timeout", "90m",
      "lake", "-d", path.join(checkout, "proofs", "talos", "lean"), "update",
    ], { cwd: checkout });
    await run([
      "git", "-C",
      path.join(checkout, "proofs", "talos", "lean", ".lake", "packages", "CodeLib"),
      "submodule", "update", "--init", "vendor/testsuite",
    ], { cwd: checkout });
    await checkDependencyRevisions(checkout, evidence);
    await requireCleanCheckout(checkout, "after dependency setup");
    compareReleaseInputs(expectedInputs, collectReleaseInputs(checkout));
    await run(["tools/artifact-proof.js", "check-all"], { cwd: checkout });
    await run(["tools/artifact-conformance.js", "check"], { cwd: checkout });
    await requireCleanCheckout(checkout, "after release gates");
    compareReleaseInputs(expectedInputs, collectReleaseInputs(checkout));
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true, force: true });
  }
  const receipt = {
    schemaVersion: 1,
    sourceRevision: revision,
    releaseInputSha256: expectedInputs.sha256,
    date: currentLocalDate(),
    artifactProof: "passed",
    semanticConformance: readJson(conformancePath).knownIssues.length === 0
      ? "passed"
      : "passed-with-warning",
  };
  writeJsonAtomic(path.join(receiptRoot, "cold-checkout.json"), receipt);
  console.log(JSON.stringify(receipt));
}

async function checkKernel(toolchain, evidence) {
  const version = await spawnResultAsync([
    path.join(repoRoot, "tools", "leanrun"),
    "--timeout", "2m", "--toolchain", toolchain, "lean", "--version",
  ], { cwd: repoRoot });
  if (version.status !== 0) fail("candidate Lean version check failed");
  const versionText = version.stdout.toString("utf8").trim();
  if (!versionText.includes(`version ${evidence.kernelReview.candidateToolchain.split(":v")[1]}`) ||
      !versionText.includes(`commit ${evidence.kernelReview.candidateCommit}`)) {
    fail(`candidate Lean identity mismatch: ${versionText}`);
  }

  const reproduction = await spawnResultAsync([
    "git", "show", evidence.kernelReview.reproductionSource,
  ], { cwd: repoRoot });
  if (reproduction.status !== 0) fail("could not read the recorded kernel reproduction");
  if (sha256(reproduction.stdout) !== evidence.kernelReview.reproductionSha256) {
    fail("kernel reproduction identity mismatch");
  }

  const temporaryRoot = makeTemporaryDirectory("leanexe-kernel-");
  const source = path.join(temporaryRoot, "KernelUnsoundness.lean");
  try {
    fs.writeFileSync(source, reproduction.stdout);
    const result = await spawnResultAsync([
      path.join(repoRoot, "tools", "leanrun"),
      "--timeout", "5m", "--toolchain", toolchain, "lean", source,
    ], { cwd: repoRoot });
    const output = `${result.stderr.toString("utf8")}\n${result.stdout.toString("utf8")}`;
    if (evidence.kernelReview.candidateResult === "reproduction-accepted") {
      if (result.status !== 0) {
        fail(`candidate Lean unexpectedly rejected the reproduction:\n${output.trim()}`);
      }
    } else {
      if (result.status === 0) fail("candidate Lean accepted the kernel reproduction");
      if (!output.includes("(kernel) invalid projection")) {
        fail(`candidate Lean rejected the reproduction for an unexpected reason:\n${output.trim()}`);
      }
    }
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true, force: true });
  }
  console.log(
    `Kernel check passed: ${evidence.kernelReview.candidateToolchain} ` +
    `${evidence.kernelReview.candidateCommit} (${evidence.kernelReview.candidateResult})`,
  );
}

function auditKernelScope(evidence) {
  const findings = kernelScopeFindings(repoRoot, evidence.kernelReview.scopeAudit);
  if (findings.length > 0) {
    fail(`kernel scope audit found forbidden identifiers:\n${findings.join("\n")}`);
  }
  console.log(
    `Kernel scope audit passed: ${[
      ...evidence.kernelReview.scopeAudit.roots,
      ...evidence.kernelReview.scopeAudit.sources,
    ].join(", ")}`,
  );
}

async function main() {
  if (process.argv.length === 3 && process.argv[2] === "input-identity") {
    const inputs = collectReleaseInputs(repoRoot);
    console.log(JSON.stringify(inputs, null, 2));
    return;
  }
  if (process.argv.length === 3 && process.argv[2] === "refresh") {
    const evidence = refreshEvidence();
    const blockers = validateEvidence(evidence);
    console.log(
      `Artifact release evidence refreshed: ${evidence.packages.length} packages, ` +
      `${blockers.length} blocker${blockers.length === 1 ? "" : "s"}`,
    );
    return;
  }
  const { evidence, blockers } = loadEvidence();
  if (process.argv.length === 3 && process.argv[2] === "inspect") {
    console.log(
      `Artifact release record is ${evidence.status}: ${evidence.packages.length} packages, ` +
      `${blockers.length} blocker${blockers.length === 1 ? "" : "s"}`,
    );
    for (const blocker of blockers) console.log(`blocker: ${blocker}`);
    return;
  }
  if (process.argv.length === 3 && process.argv[2] === "check-ready") {
    if (blockers.length > 0) fail(`release evidence is incomplete:\n${blockers.join("\n")}`);
    console.log(`Artifact release record is ready: ${evidence.packages.length} packages`);
    return;
  }
  if (process.argv.length === 4 && process.argv[2] === "check-cold") {
    await checkCold(process.argv[3], evidence);
    return;
  }
  if (process.argv.length === 4 && process.argv[2] === "check-kernel") {
    await checkKernel(process.argv[3], evidence);
    return;
  }
  if (process.argv.length === 3 && process.argv[2] === "audit-kernel-scope") {
    auditKernelScope(evidence);
    return;
  }
  fail("usage: artifact-release.js inspect|input-identity|refresh|check-ready|check-cold <revision>|check-kernel <toolchain-directory>|audit-kernel-scope");
}

if (require.main === module) {
  main().catch((error) => {
    console.error(`artifact-release.js: ${error.message}`);
    process.exitCode = 1;
  });
}

module.exports = {
  derivedBlockers,
  kernelScopeFindings,
  loadEvidence,
  refreshEvidence,
  requireCleanCheckout,
  validateEvidence,
};
