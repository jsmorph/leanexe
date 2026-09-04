#!/usr/bin/env node
"use strict";

const childProcess = require("node:child_process");
const fs = require("node:fs");
const path = require("node:path");
const {
  buildDataset,
  checkPublishedDataset,
  dataset,
  evidenceClassification,
  fileIdentity,
  formalProof,
  gitBlobSha1,
  generatorIdentity,
  generatorIdentityScheme,
  generatorSourcePaths,
  isFiniteBinary64Word,
  lanyonColumns,
  lanyonCommit,
  lanyonCommitTree,
  lanyonEvaluated,
  lanyonLicenseByteLength,
  lanyonLicenseGitBlob,
  lanyonLicensePath,
  lanyonLicenseSha256,
  lanyonMetadataPath,
  lanyonNotEvaluated,
  lanyonRepository,
  lanyonSourceByteLength,
  lanyonSourceGitBlob,
  lanyonSourcePath,
  lanyonSourceSha256,
  linkFlags,
  mirrorRelation,
  mirrorSourcePath,
  readUpstreamMetadata,
  schema,
  sha256,
  strictCFlags,
  validatePinnedUpstream,
} = require("../tools/euler-rusanov-c-compare");

const repoRoot = path.resolve(__dirname, "..");
const expectedCsvSha256 = "21a95065f98f8f3e88962f7545af27b7e7fe8dca9084dfefba048e2d40e78a7e";
const expectedRowOrder = Object.freeze([
  "sod_ll",
  "sod_rr",
  "sod_lr",
  "sod_rl",
  "moving_consistency",
  "guard_min_to_max",
  "guard_max_to_min",
  "nan_rejected",
]);
const expectedLanyonColumns = Object.freeze([
  "lanyon_rho_l_bits",
  "lanyon_mom_l_bits",
  "lanyon_energy_l_bits",
  "lanyon_rho_r_bits",
  "lanyon_mom_r_bits",
  "lanyon_energy_r_bits",
  "lanyon_dynamic_alpha_bits",
  "lanyon_flux_from_left_mass_bits",
  "lanyon_flux_from_left_momentum_bits",
  "lanyon_flux_from_left_energy_bits",
  "lanyon_flux_from_right_mass_bits",
  "lanyon_flux_from_right_momentum_bits",
  "lanyon_flux_from_right_energy_bits",
]);
const expectedSchema = Object.freeze([
  "case",
  "rho_l_bits",
  "u_l_bits",
  "p_l_bits",
  "rho_r_bits",
  "u_r_bits",
  "p_r_bits",
  "verified_wasm_status_u64",
  "verified_wasm_mass_bits",
  "verified_wasm_momentum_bits",
  "verified_wasm_energy_bits",
  "mirror_status_u64",
  "mirror_mass_bits",
  "mirror_momentum_bits",
  "mirror_energy_bits",
  "mirror_relation",
  "lanyon_evaluation",
  ...expectedLanyonColumns,
]);
const expectedStrictCFlags = Object.freeze([
  "-std=c11",
  "-O0",
  "-Wall",
  "-Wextra",
  "-Wpedantic",
  "-Werror",
  "-fno-fast-math",
  "-ffp-contract=off",
  "-frounding-math",
  "-fno-associative-math",
  "-fno-reciprocal-math",
  "-fno-finite-math-only",
  "-fno-unsafe-math-optimizations",
  "-fexcess-precision=standard",
]);

function render(value) {
  return typeof value === "bigint" ? value.toString(10) : JSON.stringify(value);
}

function requireEqual(label, actual, expected) {
  if (actual !== expected) {
    throw new Error(`${label}: expected ${render(expected)}, got ${render(actual)}`);
  }
}

function requireJsonEqual(label, actual, expected) {
  requireEqual(label, JSON.stringify(actual), JSON.stringify(expected));
}

function requireFileIdentity(label, relativePath, expectedByteLength, expectedSha256) {
  const identity = fileIdentity(relativePath);
  requireEqual(`${label} path`, identity.path, relativePath);
  requireEqual(`${label} byte length`, identity.byteLength, expectedByteLength);
  requireEqual(`${label} SHA-256`, identity.sha256, expectedSha256);
  return identity;
}

async function main() {
  const built = await buildDataset();
  checkPublishedDataset(built);

  requireEqual("dataset identifier", dataset, "euler-rusanov-c-comparison-v1");
  requireEqual("evidence classification", evidenceClassification, "regression-only");
  requireEqual("formal proof", formalProof, null);
  requireEqual("fixed-alpha mirror invocation count", built.mirrorInvocationCount, 8);
  requireEqual("Lanyon invocation count", built.lanyonInvocationCount, 7);
  requireJsonEqual("schema", schema, expectedSchema);
  requireJsonEqual("Lanyon column order", lanyonColumns, expectedLanyonColumns);
  requireJsonEqual("row order", built.rows.map((row) => row.name), expectedRowOrder);
  requireJsonEqual("strict C flags", strictCFlags, expectedStrictCFlags);
  requireJsonEqual("C link flags", linkFlags, ["-lm"]);

  requireEqual("CSV terminates in one LF", built.csv.endsWith("\n") && !built.csv.endsWith("\n\n"), true);
  requireEqual("CSV carriage-return count", (built.csv.match(/\r/g) || []).length, 0);
  requireEqual("CSV SHA-256", sha256(Buffer.from(built.csv, "utf8")), expectedCsvSha256);
  const lines = built.csv.slice(0, -1).split("\n");
  requireEqual("CSV physical line count", lines.length, 9);
  requireEqual("CSV header", lines[0], expectedSchema.join(","));

  let hasDistinctLanyonReconstructions = false;
  for (const [index, row] of built.rows.entries()) {
    const fields = lines[index + 1].split(",");
    requireEqual(`${row.name} CSV field count`, fields.length, expectedSchema.length);
    requireEqual(`${row.name} CSV case`, fields[0], row.name);
    for (const word of [...row.inputs, ...row.verifiedOutputs, ...row.mirrorOutputs]) {
      if (!/^[0-9a-f]{16}$/.test(word)) {
        throw new Error(`${row.name}: noncanonical verified or mirror raw word ${JSON.stringify(word)}`);
      }
    }
    requireEqual(`${row.name} mirror status`, row.mirrorStatus, row.verifiedStatus);
    requireJsonEqual(`${row.name} mirror outputs`, row.mirrorOutputs, row.verifiedOutputs);
    requireEqual(`${row.name} mirror relation`, row.mirrorRelation, mirrorRelation);
    requireEqual(`${row.name} mirror relation value`, row.mirrorRelation, "bit_exact");

    if (row.verifiedStatus === 0n) {
      requireEqual(`${row.name} Lanyon evaluation`, row.lanyonEvaluation, lanyonEvaluated);
      requireEqual(`${row.name} Lanyon word count`, row.lanyonWords.length, 13);
      for (const [wordIndex, word] of row.lanyonWords.entries()) {
        if (!isFiniteBinary64Word(word)) {
          throw new Error(`${row.name}: Lanyon word ${wordIndex} is not canonical finite binary64`);
        }
      }
      if (JSON.stringify(row.lanyonWords.slice(7, 10)) !==
          JSON.stringify(row.lanyonWords.slice(10, 13))) {
        hasDistinctLanyonReconstructions = true;
      }
    } else {
      requireEqual(`${row.name} rejected case`, row.name, "nan_rejected");
      requireEqual(`${row.name} verified status`, row.verifiedStatus, 1n);
      requireEqual(`${row.name} Lanyon evaluation`, row.lanyonEvaluation, lanyonNotEvaluated);
      requireJsonEqual(`${row.name} missing Lanyon values`, row.lanyonWords, Array(13).fill(""));
    }
  }
  requireEqual("at least one Lanyon row retains distinct rounded reconstructions",
    hasDistinctLanyonReconstructions, true);

  const rejectedRow = built.rows.find((row) => row.name === "nan_rejected");
  const rejectedRun = childProcess.spawnSync(
    built.compiled.lanyonExecutable,
    rejectedRow.inputs,
    { cwd: repoRoot, encoding: "utf8" },
  );
  if (rejectedRun.error) {
    throw rejectedRun.error;
  }
  requireEqual("rejected-row Lanyon adapter exit status", rejectedRun.status, 2);
  requireEqual("rejected-row Lanyon adapter stdout", rejectedRun.stdout, "");
  requireEqual(
    "rejected-row Lanyon adapter diagnostic names the adapter",
    rejectedRun.stderr.includes("verified-dyadic-conservative-v1"),
    true,
  );

  const manifest = JSON.parse(built.manifest);
  requireEqual("manifest schema version", manifest.schemaVersion, 1);
  requireEqual("manifest dataset", manifest.dataset, dataset);
  requireEqual("manifest evidence classification", manifest.evidenceClassification, "regression-only");
  requireEqual("manifest formal proof", manifest.formalProof, null);
  requireJsonEqual("manifest CSV schema", manifest.csvSchema, expectedSchema);
  requireEqual("manifest row count", manifest.rowCount, 8);
  requireJsonEqual("manifest row order", manifest.rowOrder, expectedRowOrder);
  requireEqual("manifest CSV file", manifest.csvFile, "c-comparison-v1.csv");
  requireEqual("manifest CSV byte length", manifest.csvByteLength, Buffer.byteLength(built.csv, "utf8"));
  requireEqual("manifest CSV SHA-256", manifest.csvSha256, expectedCsvSha256);
  requireEqual("manifest encoding", manifest.encoding, "UTF-8");
  requireEqual("manifest line endings", manifest.lineEndings, "LF");

  const source = manifest.sourceInterfaceDataset;
  requireEqual("source interface dataset", source.dataset, "euler-rusanov-interface-v1");
  requireEqual("source interface CSV byte length", source.csvByteLength, 1444);
  requireEqual("source interface CSV SHA-256", source.csvSha256, "65ff256da20d19544366083596f20b53c4fb37798209c1e7e16c2cfcee4d3808");
  requireEqual("source interface manifest byte length", source.manifestByteLength, 2408);
  requireEqual("source interface manifest SHA-256", source.manifestSha256, "fa39e7314a5c0709c7e8636df63731cd1649709f7e97c5ee700f9ef89d624118");
  requireEqual("source interface registry entry", source.registryEntry, "euler_rusanov");
  requireEqual("source interface WASM SHA-256", source.wasmSha256, "145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546");
  requireEqual("source interface WASM byte length", source.wasmByteLength, 1808);
  requireEqual("source interface export", source.exportedFunction, "rusanovFluxCheckedBits");
  requireEqual("source interface proof module", source.formalProofModule, "Project.EulerRusanov.InterfaceData");
  requireEqual("source interface proof theorem", source.formalProofTheorem, "Project.EulerRusanov.InterfaceData.artifact_interfaceV1");
  requireEqual(
    "source interface execution method",
    source.executionMethod,
    "external Wasmtime CLI through the source interface generator; no JavaScript WebAssembly API",
  );

  const mirrorPolicy = manifest.comparisonPolicy.fixedAlphaMirror;
  requireEqual("mirror policy classification", mirrorPolicy.classification, "regression-only");
  requireEqual("mirror required relation", mirrorPolicy.requiredRelation, "bit_exact");
  requireEqual("mirror evaluated rows", mirrorPolicy.evaluatedRows, 8);
  const lanyonPolicy = manifest.comparisonPolicy.lanyon;
  requireEqual("Lanyon policy classification", lanyonPolicy.classification, "regression-only");
  requireEqual("Lanyon portability", lanyonPolicy.portability, "supported-host regression snapshot; not portable numerical truth");
  requireEqual("Lanyon equality claim", lanyonPolicy.equalityClaim, null);
  requireEqual("Lanyon evaluated marker", lanyonPolicy.evaluatedMarker, "evaluated");
  requireEqual("Lanyon rejected marker", lanyonPolicy.notEvaluatedMarker, "not_evaluated_guard_rejected");
  requireEqual("Lanyon missing-value policy", lanyonPolicy.missingValueEncoding, "thirteen empty CSV fields");
  requireEqual("Lanyon evaluated rows", lanyonPolicy.evaluatedRows, 7);
  requireJsonEqual("Lanyon non-evaluated rows", lanyonPolicy.notEvaluatedRows, ["nan_rejected"]);
  requireEqual("Lanyon finite-word policy", lanyonPolicy.finiteWordsRequiredForEvaluatedRows, true);
  requireEqual(
    "Lanyon dual reconstruction policy",
    lanyonPolicy.outputPolicy,
    "report both reconstructed numerical fluxes; do not average, select, or require equality",
  );
  requireJsonEqual("manifest Lanyon column order", manifest.lanyonOutputColumns, expectedLanyonColumns);

  requireEqual("verified exact gamma", manifest.parameters.verifiedRealGamma, "7/5 (exact)");
  requireEqual("Lanyon gamma C expression", manifest.parameters.lanyonGasGamma.cExpression, "7.0 / 5.0");
  requireEqual("Lanyon gamma binary64 word", manifest.parameters.lanyonGasGamma.binary64Bits, "3ff6666666666666");

  const compiler = manifest.compilerContract;
  requireEqual("compiler executable", compiler.executable, "cc");
  requireEqual("compiler language", compiler.language, "C11");
  requireJsonEqual("compiler flags", compiler.flags, expectedStrictCFlags);
  requireJsonEqual("mirror link flags", compiler.mirrorLinkFlags, ["-lm"]);
  requireJsonEqual("Lanyon link flags", compiler.lanyonLinkFlags, ["-lm"]);
  requireEqual("floating-point environment", compiler.floatingPointEnvironment, "IEC 60559 binary64, FE_TONEAREST");
  requireEqual("platform check count", compiler.platformChecks.length, 6);
  requireEqual("compiler binary identity deliberately absent", compiler.compilerBinaryIdentity, null);

  requireFileIdentity(
    "fixed-alpha mirror source",
    mirrorSourcePath,
    8269,
    "05299ed73f677833f1047bf5160c5f05da2b2d785f81d39a93db23516e57f252",
  );
  const driverIdentity = requireFileIdentity(
    "Lanyon driver source",
    "test/fixtures/euler-rusanov-c/lanyon-driver.c",
    7996,
    "8b75570129c8e823b19f36ffe4b50579e149c19243121b2824a8d088508a12ac",
  );
  requireJsonEqual("manifest mirror source identity", manifest.cSources.fixedAlphaMirror, fileIdentity(mirrorSourcePath));
  requireJsonEqual("manifest Lanyon driver identity", manifest.cSources.lanyonDriver, driverIdentity);
  requireFileIdentity("Lanyon upstream source", lanyonSourcePath, lanyonSourceByteLength, lanyonSourceSha256);
  requireFileIdentity("Lanyon upstream license", lanyonLicensePath, lanyonLicenseByteLength, lanyonLicenseSha256);
  requireFileIdentity(
    "Lanyon upstream metadata",
    lanyonMetadataPath,
    867,
    "668d8562a7845f6a967b0694dc2e86514fc5f9fc85a0afa28898f62ba77acf95",
  );

  const upstream = manifest.cSources.lanyonUpstream;
  requireEqual("Lanyon repository", upstream.repository, lanyonRepository);
  requireEqual("Lanyon commit", upstream.commit, lanyonCommit);
  requireEqual("Lanyon commit tree", upstream.metadataValue.commitTree, lanyonCommitTree);
  requireEqual("Lanyon source Git blob", upstream.source.gitBlobSha1, lanyonSourceGitBlob);
  requireEqual("recomputed Lanyon source Git blob", gitBlobSha1(lanyonSourcePath), lanyonSourceGitBlob);
  requireEqual("Lanyon source bytes", upstream.source.byteLength, 27229);
  requireEqual("Lanyon source SHA-256", upstream.source.sha256, lanyonSourceSha256);
  requireEqual("Lanyon license Git blob", upstream.license.gitBlobSha1, lanyonLicenseGitBlob);
  requireEqual("recomputed Lanyon license Git blob", gitBlobSha1(lanyonLicensePath), lanyonLicenseGitBlob);
  requireEqual("Lanyon license bytes", upstream.license.byteLength, 1070);
  requireEqual("Lanyon license SHA-256", upstream.license.sha256, lanyonLicenseSha256);
  requireJsonEqual("embedded upstream metadata", upstream.metadataValue, built.upstreamMetadata);
  validatePinnedUpstream(readUpstreamMetadata());

  const identity = generatorIdentity();
  requireEqual("generator identity scheme", identity.scheme, generatorIdentityScheme);
  requireJsonEqual("generator source order", generatorSourcePaths, [...generatorSourcePaths].sort());
  requireJsonEqual("manifest generator identity", manifest.generatorIdentity, identity);
  requireEqual("manifest generator revision", manifest.generatorRevision, `sha256:${identity.sha256}`);
  requireEqual("manifest terminates in LF", built.manifest.endsWith("\n"), true);
  requireEqual("manifest carriage-return count", (built.manifest.match(/\r/g) || []).length, 0);

  const generatorSource = fs.readFileSync(
    path.join(repoRoot, "tools", "euler-rusanov-c-compare.js"),
    "utf8",
  );
  const blockedApiIdentifier = ["Web", "Assembly"].join("");
  const directExecutionPattern = new RegExp(
    `${blockedApiIdentifier}\\s*\\.\\s*(?:instantiate|instantiateStreaming|Module|Instance)`,
  );
  requireEqual(
    "comparison generator avoids direct JavaScript WebAssembly execution",
    directExecutionPattern.test(generatorSource),
    false,
  );

  process.stdout.write(
    "checked Euler Rusanov C regression: 8/8 exact mirror rows, 7 finite pinned-Lanyon rows, identities, policies, LF CSV, and manifest\n",
  );
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exitCode = 1;
});
