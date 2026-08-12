#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { runCheckedAsync, spawnResultAsync } = require("./run-process");
const {
  loadArtifactRegistry,
  sha256,
  validateArtifactManifest,
} = require("./artifact-manifest");
const { collectReleaseInputs } = require("./artifact-identity");
const { currentLocalDate } = require("./date");
const { makeTemporaryDirectory } = require("./temp-directory");

const repoRoot = path.resolve(__dirname, "..");
const artifactRoot = path.join(repoRoot, "proofs", "artifacts");
const proofRoot = path.join(repoRoot, "proofs", "talos", "lean");
const leanrun = path.join(repoRoot, "tools", "leanrun");
const checkFile = path.join(
  proofRoot,
  "Project",
  "Artifact",
  "Binary",
  "CheckFile.lean",
);
const receiptPath = path.join(repoRoot, "build", "evidence", "artifact-proof.json");
const allowedAxioms = new Set([
  "propext",
  "Classical.choice",
  "Quot.sound",
  "Lean.ofReduceBool",
]);
const generatedDecisionAxiom =
  /^[A-Za-z0-9_.]+\._native\.(?:native_decide|bv_decide)\.ax_[0-9_]+$/;

function fail(message) {
  throw new Error(message);
}

function writeReceipt(file, value) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  const temporary = `${file}.tmp-${process.pid}`;
  fs.writeFileSync(temporary, `${JSON.stringify(value, null, 2)}\n`);
  fs.renameSync(temporary, file);
}

async function run(stage, args) {
  try {
    await runCheckedAsync([leanrun, ...args], {
      cwd: repoRoot,
      env: process.env,
      stdio: "inherit",
    });
  } catch (error) {
    fail(`${stage}: ${error.message}`);
  }
}

function loadRegistry() {
  return loadArtifactRegistry(repoRoot).registry.artifacts;
}

function selectEntry(entries, proofTarget) {
  const selected = entries.find((entry) => entry.proofTarget === proofTarget);
  if (!selected) fail(`unregistered proof target: ${proofTarget}`);
  return selected;
}

function validateManifest(entry) {
  return validateArtifactManifest(repoRoot, entry);
}

function checkBytes(entry, manifest, manifestPath, inputPath) {
  const packagePath = path.join(path.dirname(manifestPath), "program.wasm");
  const packaged = fs.readFileSync(packagePath);
  const input = fs.readFileSync(inputPath);
  for (const [description, bytes] of [["package", packaged], ["input", input]]) {
    const found = sha256(bytes);
    if (found !== manifest.sha256) {
      fail(`${description} SHA-256 mismatch: expected ${manifest.sha256}, found ${found}`);
    }
    if (bytes.length !== manifest.byteLength) {
      fail(`${description} length mismatch: expected ${manifest.byteLength}, found ${bytes.length}`);
    }
  }
  if (!packaged.equals(input)) fail("input bytes differ from the frozen package");
  console.log(`Artifact identity passed: ${entry.case} ${manifest.sha256}`);
  return packagePath;
}

async function checkEmbedded(packages) {
  for (const item of packages) {
    await run(`embedded byte module ${item.entry.case}`, [
      "--timeout", "30m",
      "lake", "-d", proofRoot, "build", item.manifest.artifactBytesModule,
    ]);
  }
  await run("embedded byte checker", [
    "--timeout", "15m",
    "lake", "-d", proofRoot, "build", "Project.Artifact.Binary.CheckFile",
  ]);
  const args = [
    "--timeout", "15m",
    "lake", "-d", proofRoot, "env", "lean", "--run", checkFile,
  ];
  for (const item of packages) args.push(item.entry.case, item.packagePath);
  await run("embedded byte comparison", args);
}

async function buildArtifact(item) {
  const artifactPrefix = item.manifest.artifactBytesModule.replace(/\.ArtifactBytes$/u, "");
  const candidates = [
    item.manifest.cachedProgramModule,
    `${artifactPrefix}.ArtifactDecoded`,
    `${artifactPrefix}.ArtifactRawCache`,
    `${artifactPrefix}.ArtifactDecode`,
    `${artifactPrefix}.ArtifactValidation`,
    `${artifactPrefix}.Artifact`,
  ];
  const inputs = candidates.filter((target) => fs.existsSync(
    path.join(proofRoot, `${target.replaceAll(".", path.sep)}.lean`),
  ));
  for (const target of inputs) {
    await run(`artifact proof input ${target}`, [
      "--timeout", "30m",
      "lake", "-d", proofRoot, "build", target,
    ]);
  }
  await run("artifact proof", [
    "--timeout", "15m",
    "lake", "-d", proofRoot, "build", item.entry.proofTarget,
  ]);
  console.log(`Artifact theorem passed: ${item.entry.case} ${item.entry.proofTarget}`);
}

async function buildSpecification(item) {
  await run("behavioral specification", [
    "--timeout", "60m",
    "lake", "-d", proofRoot, "build", item.manifest.specModule,
  ]);
  console.log(`Behavioral specification passed: ${item.entry.case} ${item.manifest.specModule}`);
}

async function checkDeclarations(items) {
  await run("manifest theorem dependencies", [
    "--timeout", "15m",
    "lake", "-d", proofRoot, "build",
    "Project.Artifact.Binary.Proof.Decode",
    "Project.Artifact.Binary.Proof.Validate",
  ]);
  const temporaryRoot = makeTemporaryDirectory("leanexe-artifact-");
  const source = path.join(temporaryRoot, "CheckDeclarations.lean");
  const modules = new Set([
    "Project.Artifact.Binary.Proof.Decode",
    "Project.Artifact.Binary.Proof.Validate",
  ]);
  const checks = [];
  const theorems = new Set();
  for (const item of items) {
    modules.add(item.manifest.artifactBytesModule);
    modules.add(item.manifest.cachedProgramModule);
    modules.add(item.manifest.proofTarget);
    modules.add(item.manifest.specModule);
    const cachedProgram = item.manifest.cachedProgramDefinition.replace(
      /\.module$/, ".«module»",
    );
    checks.push(
      `example : Wasm.Binary.decode ${item.manifest.artifactBytesDefinition} =\n` +
        `    .ok ${item.manifest.rawModuleDefinition} :=\n` +
        `  ${item.manifest.identityTheorem}`,
      `example : Wasm.Binary.Translation.module ${item.manifest.rawModuleDefinition} =\n` +
        `    ${cachedProgram} :=\n` +
        `  ${item.manifest.cacheEqualityTheorem}`,
      `example :\n` +
        `    ∃ raw validated,\n` +
        `      Wasm.Binary.decode ${item.manifest.artifactBytesDefinition} = .ok raw ∧\n` +
        `      Wasm.Binary.validate raw = .ok validated ∧\n` +
        `      Wasm.Binary.CoreValid raw ∧\n` +
        `      validated.toTalos = ${cachedProgram} :=\n` +
        `  ${item.manifest.artifactCorrectnessTheorem}`,
    );
    for (const theorem of [
      item.manifest.identityTheorem,
      item.manifest.decodeTheorem,
      item.manifest.validationTheorem,
      item.manifest.cacheEqualityTheorem,
      item.manifest.artifactCorrectnessTheorem,
      ...item.manifest.behaviorTheorems,
    ]) theorems.add(theorem);
  }
  try {
    const text = [
      ...[...modules].map((module) => `import ${module}`),
      "",
      `example {bytes : ByteArray} {module_ : Wasm.Binary.RawModule}`,
      `    (h : Wasm.Binary.decode bytes = .ok module_) :`,
      `    Wasm.Binary.Grammar.Encodes bytes module_ :=`,
      `  ${items[0].manifest.decodeTheorem} h`,
      "",
      `example {module_ : Wasm.Binary.RawModule} {validated : Wasm.Binary.ValidatedModule}`,
      `    (h : Wasm.Binary.validate module_ = .ok validated) :`,
      `    Wasm.Binary.CoreValid module_ :=`,
      `  ${items[0].manifest.validationTheorem} h`,
      "",
      ...checks.flatMap((check) => [check, ""]),
      ...[...theorems].map((theorem) => `#print axioms ${theorem}`),
      "",
    ].join("\n");
    fs.writeFileSync(source, text);
    const result = await spawnResultAsync([leanrun,
      "--timeout", "15m",
      "lake", "-d", proofRoot, "env", "lean", source,
    ], { cwd: repoRoot, env: process.env });
    const stdout = result.stdout.toString("utf8");
    const stderr = result.stderr.toString("utf8");
    if (result.status !== 0) {
      fail(`manifest theorem check failed with exit status ${result.status}:\n${stderr}${stdout}`);
    }
    const output = `${stdout}\n${stderr}`;
    if (/\bsorryAx\b/.test(output)) {
      fail("manifest theorem check found a dependency on sorryAx");
    }
    const unexpectedAxioms = new Set();
    for (const report of output.matchAll(/depends on axioms:\s*\[([^\]]*)\]/g)) {
      for (const printedName of report[1].split(",").map((item) => item.trim()).filter(Boolean)) {
        const name = printedName.replace(/✝+$/, "");
        if (!allowedAxioms.has(name) && !generatedDecisionAxiom.test(name)) {
          unexpectedAxioms.add(printedName);
        }
      }
    }
    if (unexpectedAxioms.size > 0) {
      fail(`manifest theorem check found unsupported axioms: ${[...unexpectedAxioms].join(", ")}`);
    }
    const printed = (output.match(/(?:depends on axioms|does not depend on any axioms)/g) || []).length;
    if (printed !== theorems.size) {
      fail(`manifest theorem check printed ${printed} axiom reports for ${theorems.size} theorems`);
    }
    process.stdout.write(stdout);
    process.stderr.write(stderr);
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true, force: true });
  }
}

function prepare(entry, inputPath) {
  const { manifest, manifestPath } = validateManifest(entry);
  const packagePath = checkBytes(entry, manifest, manifestPath, inputPath);
  return { entry, manifest, manifestPath, packagePath };
}

async function main() {
  const entries = loadRegistry();
  if (process.argv.length === 3 &&
      (process.argv[2] === "check-all" || process.argv[2] === "check-artifacts")) {
    const items = entries.map((entry) => {
      const inputPath = path.join(artifactRoot, path.dirname(entry.manifest), "program.wasm");
      return prepare(entry, inputPath);
    });
    await checkEmbedded(items);
    for (const item of items) await buildArtifact(item);
    if (process.argv[2] === "check-artifacts") {
      console.log(`Aggregate artifact theorem pass completed: ${items.length} artifacts`);
      return;
    }
    for (const item of items) await buildSpecification(item);
    await checkDeclarations(items);
    console.log(`Aggregate artifact proof passed: ${items.length} artifacts`);
    const receipt = {
      schemaVersion: 1,
      date: currentLocalDate(),
      result: "passed",
      artifactCount: items.length,
      releaseInputSha256: collectReleaseInputs(repoRoot).sha256,
    };
    writeReceipt(receiptPath, receipt);
    console.log(`ARTIFACT_PROOF_RECEIPT ${JSON.stringify(receipt)}`);
    return;
  }
  if (process.argv.length !== 5 || process.argv[2] !== "check") {
    fail("usage: artifact-proof.js check <program.wasm> <proof-target>\n       artifact-proof.js check-artifacts\n       artifact-proof.js check-all");
  }
  const inputPath = path.resolve(process.argv[3]);
  const proofTarget = process.argv[4];
  const item = prepare(selectEntry(entries, proofTarget), inputPath);
  await checkEmbedded([item]);
  await buildArtifact(item);
  await buildSpecification(item);
  await checkDeclarations([item]);
}

main().catch((error) => {
  console.error(`artifact-proof.js: ${error.message}`);
  process.exitCode = 1;
});
