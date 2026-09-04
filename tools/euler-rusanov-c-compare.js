#!/usr/bin/env node
"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const {
  artifactByteLength,
  artifactCase,
  artifactSha256,
  buildDataset: buildInterfaceDataset,
  checkPublishedDataset: checkPublishedInterfaceDataset,
  csvPath: interfaceCsvPath,
  dataManifestPath: interfaceManifestPath,
  dataset: interfaceDataset,
  exportedFunction,
  frozenRows,
  formalProofModule: interfaceFormalProofModule,
  formalProofTheorem: interfaceFormalProofTheorem,
  sha256,
} = require("./euler-rusanov-interface");
const { runChecked } = require("./run-process");

const repoRoot = path.resolve(__dirname, "..");
const fixtureDirectory = path.join(repoRoot, "test", "fixtures", "euler-rusanov-c");
const buildDirectory = path.join(repoRoot, "build", "tests", "euler-rusanov-c");
const outputDirectory = path.join(
  repoRoot,
  "data",
  "euler-rusanov-interface-v1",
  "regression",
);
const csvPath = path.join(outputDirectory, "c-comparison-v1.csv");
const dataManifestPath = path.join(outputDirectory, "manifest.json");

const dataset = "euler-rusanov-c-comparison-v1";
const evidenceClassification = "regression-only";
const formalProof = null;
const lanyonCommit = "a736aa5f8b17efd225c4692404e2442361d06729";
const lanyonCommitTree = "373f81b54f06e4bca04d06999e95882e42428ad7";
const lanyonRepository = "https://github.com/lanyonai/CompressibleEuler";
const lanyonSourceGitBlob = "fbd70a9407d02ce2e49b6d6f37152c70ca679de4";
const lanyonSourceByteLength = 27229;
const lanyonSourceSha256 = "f1f284f550d790c88f293e1d67a91434dc9b8c6187f88caed0f776c5039cf756";
const lanyonLicenseGitBlob = "16b2ed3f9bee8eeb7bd7291ea6dfef76675b7e32";
const lanyonLicenseByteLength = 1070;
const lanyonLicenseSha256 = "cfa90e3adf9a116fe3959a57353acdf5b6a783d3442d0e5a0834627990370116";
const lanyonEvaluated = "evaluated";
const lanyonNotEvaluated = "not_evaluated_guard_rejected";
const mirrorRelation = "bit_exact";
const generatorIdentityScheme = "leanexe-euler-rusanov-c-comparison-generator-v1";

const mirrorSourcePath = "test/fixtures/euler-rusanov-c/fixed-alpha-mirror.c";
const lanyonDriverPath = "test/fixtures/euler-rusanov-c/lanyon-driver.c";
const lanyonDirectoryPath = `test/fixtures/euler-rusanov-c/lanyon/${lanyonCommit}`;
const lanyonSourcePath = `${lanyonDirectoryPath}/compressible_euler_1d.c`;
const lanyonLicensePath = `${lanyonDirectoryPath}/LICENSE`;
const lanyonMetadataPath = `${lanyonDirectoryPath}/upstream.json`;
const fixtureReadmePath = "test/fixtures/euler-rusanov-c/README.md";

const generatorSourcePaths = Object.freeze([
  fixtureReadmePath,
  mirrorSourcePath,
  lanyonDriverPath,
  lanyonLicensePath,
  lanyonSourcePath,
  lanyonMetadataPath,
  "tools/artifact-manifest.js",
  "tools/euler-rusanov-c-compare.js",
  "tools/euler-rusanov-interface.js",
  "tools/run-process.js",
  "tools/wasmtime-host.js",
]);

const strictCFlags = Object.freeze([
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
const linkFlags = Object.freeze(["-lm"]);

const lanyonColumns = Object.freeze([
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

const schema = Object.freeze([
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
  ...lanyonColumns,
]);

function requireEqual(label, actual, expected) {
  if (actual !== expected) {
    const render = (value) => typeof value === "bigint" ? value.toString(10) : JSON.stringify(value);
    throw new Error(`${label}: expected ${render(expected)}, got ${render(actual)}`);
  }
}

function absolutePath(relative) {
  return path.join(repoRoot, ...relative.split("/"));
}

function fileIdentity(relative) {
  const bytes = fs.readFileSync(absolutePath(relative));
  return {
    path: relative,
    byteLength: bytes.length,
    sha256: sha256(bytes),
  };
}

function gitBlobSha1(relative) {
  const bytes = fs.readFileSync(absolutePath(relative));
  const hash = crypto.createHash("sha1");
  hash.update(`blob ${bytes.length}\0`);
  hash.update(bytes);
  return hash.digest("hex");
}

function generatorIdentity() {
  const sources = [...generatorSourcePaths].sort().map((relative) => {
    const bytes = fs.readFileSync(absolutePath(relative));
    return {
      path: relative,
      byteLength: bytes.length,
      sha256: sha256(bytes),
      bytes,
    };
  });
  const hash = crypto.createHash("sha256");
  hash.update(`${generatorIdentityScheme}\0`);
  for (const source of sources) {
    hash.update(`${source.path}\0${source.byteLength}\0`);
    hash.update(source.bytes);
  }
  return {
    scheme: generatorIdentityScheme,
    sources: sources.map(({ path: sourcePath, byteLength, sha256: sourceSha256 }) => ({
      path: sourcePath,
      byteLength,
      sha256: sourceSha256,
    })),
    sha256: hash.digest("hex"),
  };
}

function readUpstreamMetadata() {
  const text = fs.readFileSync(absolutePath(lanyonMetadataPath), "utf8");
  if (text.includes("\r")) {
    throw new Error(`${lanyonMetadataPath} contains a non-LF line ending`);
  }
  return JSON.parse(text);
}

function validatePinnedUpstream(upstreamMetadata) {
  const sourceIdentity = fileIdentity(lanyonSourcePath);
  const licenseIdentity = fileIdentity(lanyonLicensePath);
  requireEqual("Lanyon source byte length", sourceIdentity.byteLength, lanyonSourceByteLength);
  requireEqual("Lanyon source SHA-256", sourceIdentity.sha256, lanyonSourceSha256);
  requireEqual("Lanyon license byte length", licenseIdentity.byteLength, lanyonLicenseByteLength);
  requireEqual("Lanyon license SHA-256", licenseIdentity.sha256, lanyonLicenseSha256);
  requireEqual("upstream metadata schema version", upstreamMetadata.schemaVersion, 1);
  requireEqual("upstream metadata repository", upstreamMetadata.repository, "lanyonai/CompressibleEuler");
  requireEqual("upstream metadata repository URL", upstreamMetadata.repositoryUrl, lanyonRepository);
  requireEqual("upstream metadata commit", upstreamMetadata.commit, lanyonCommit);
  requireEqual("upstream metadata commit tree", upstreamMetadata.commitTree, lanyonCommitTree);
  requireEqual("upstream metadata retrieval method", upstreamMetadata.retrievedFrom,
    "GitHub Git data and contents APIs");
  requireEqual("upstream metadata file count", upstreamMetadata.files.length, 2);
  const source = upstreamMetadata.files.find((file) => file.path === "compressible_euler_1d.c");
  const license = upstreamMetadata.files.find((file) => file.path === "LICENSE");
  if (!source || !license) {
    throw new Error("upstream metadata does not identify both vendored files");
  }
  requireEqual("upstream source path", source.upstreamPath, "implementations/compressible_euler_1d.c");
  requireEqual("upstream source byte length", source.byteLength, lanyonSourceByteLength);
  requireEqual("upstream source Git blob", source.gitBlobSha1, lanyonSourceGitBlob);
  requireEqual("local source Git blob", gitBlobSha1(lanyonSourcePath), lanyonSourceGitBlob);
  requireEqual("upstream source SHA-256", source.sha256, lanyonSourceSha256);
  requireEqual("upstream license path", license.upstreamPath, "LICENSE");
  requireEqual("upstream license byte length", license.byteLength, lanyonLicenseByteLength);
  requireEqual("upstream license Git blob", license.gitBlobSha1, lanyonLicenseGitBlob);
  requireEqual("local license Git blob", gitBlobSha1(lanyonLicensePath), lanyonLicenseGitBlob);
  requireEqual("upstream license SHA-256", license.sha256, lanyonLicenseSha256);
}

function compilerCommand(source, output, extraFlags = []) {
  return [
    "cc",
    ...strictCFlags,
    source,
    "-o",
    output,
    ...extraFlags,
  ];
}

function compileComparators() {
  fs.mkdirSync(buildDirectory, { recursive: true });
  const mirrorExecutable = path.join(buildDirectory, "fixed-alpha-mirror");
  const lanyonExecutable = path.join(buildDirectory, "lanyon-driver");
  const mirrorCommand = compilerCommand(
    absolutePath(mirrorSourcePath),
    mirrorExecutable,
    linkFlags,
  );
  const lanyonCommand = compilerCommand(
    absolutePath(lanyonDriverPath),
    lanyonExecutable,
    linkFlags,
  );
  runChecked(mirrorCommand, { cwd: repoRoot, encoding: "utf8" });
  runChecked(lanyonCommand, { cwd: repoRoot, encoding: "utf8" });
  return {
    mirrorCommand,
    mirrorExecutable,
    lanyonCommand,
    lanyonExecutable,
  };
}

function runText(args) {
  return runChecked(args, { cwd: repoRoot, encoding: "utf8" }).stdout;
}

function parseMirrorOutput(caseName, output) {
  const match = /^([01]),([0-9a-f]{16}),([0-9a-f]{16}),([0-9a-f]{16})\n$/.exec(output);
  if (!match) {
    throw new Error(`${caseName}: fixed-alpha mirror produced a noncanonical output line`);
  }
  return {
    status: BigInt(match[1]),
    outputs: match.slice(2),
  };
}

function parseLanyonOutput(caseName, output) {
  const match = new RegExp(`^${Array(13).fill("([0-9a-f]{16})").join(",")}\\n$`).exec(output);
  if (!match) {
    throw new Error(`${caseName}: Lanyon driver produced a noncanonical 13-word output line`);
  }
  return match.slice(1);
}

function isFiniteBinary64Word(word) {
  if (!/^[0-9a-f]{16}$/.test(word)) return false;
  return ((BigInt(`0x${word}`) >> 52n) & 0x7ffn) !== 0x7ffn;
}

function csvText(rows) {
  const lines = [schema.join(",")];
  for (const row of rows) {
    lines.push([
      row.name,
      ...row.inputs,
      row.verifiedStatus.toString(10),
      ...row.verifiedOutputs,
      row.mirrorStatus.toString(10),
      ...row.mirrorOutputs,
      row.mirrorRelation,
      row.lanyonEvaluation,
      ...row.lanyonWords,
    ].join(","));
  }
  return `${lines.join("\n")}\n`;
}

function relativeFile(file) {
  return path.relative(repoRoot, file).split(path.sep).join("/");
}

function manifestText(interfaceBuilt, rows, csv, identity, upstreamMetadata) {
  const interfaceCsv = Buffer.from(interfaceBuilt.csv, "utf8");
  const interfaceManifest = Buffer.from(interfaceBuilt.manifest, "utf8");
  const rawWordColumns = schema.filter((column) => column.endsWith("_bits"));
  const value = {
    schemaVersion: 1,
    dataset,
    evidenceClassification,
    formalProof,
    csvSchema: schema,
    rowCount: rows.length,
    rowOrder: rows.map((row) => row.name),
    sourceInterfaceDataset: {
      dataset: interfaceDataset,
      csvFile: relativeFile(interfaceCsvPath),
      csvByteLength: interfaceCsv.length,
      csvSha256: sha256(interfaceCsv),
      manifestFile: relativeFile(interfaceManifestPath),
      manifestByteLength: interfaceManifest.length,
      manifestSha256: sha256(interfaceManifest),
      registryEntry: artifactCase,
      wasmSha256: artifactSha256,
      wasmByteLength: artifactByteLength,
      exportedFunction,
      executionMethod: "external Wasmtime CLI through the source interface generator; no JavaScript WebAssembly API",
      formalProofModule: interfaceFormalProofModule,
      formalProofTheorem: interfaceFormalProofTheorem,
    },
    wordEncoding: {
      columns: rawWordColumns,
      format: "lowercase fixed-width 16-digit hexadecimal without 0x",
      semantics: "raw IEEE 754 binary64 word",
      missing: "empty field only for a deliberately unevaluated Lanyon row",
    },
    statusEncoding: {
      columns: ["verified_wasm_status_u64", "mirror_status_u64"],
      format: "minimal unsigned base-10 UInt64",
      accepted: "0",
      rejected: "1",
    },
    comparisonPolicy: {
      fixedAlphaMirror: {
        classification: "regression-only",
        method: "same fixed alpha 7/4 and same explicitly rounded operation order",
        requiredRelation: mirrorRelation,
        evaluatedRows: rows.length,
      },
      lanyon: {
        classification: "regression-only",
        portability: "supported-host regression snapshot; not portable numerical truth",
        method: "pinned dynamic-speed Lax-Friedrichs implementation using division, sqrt, fabs, and fmax",
        equalityClaim: null,
        evaluatedMarker: lanyonEvaluated,
        notEvaluatedMarker: lanyonNotEvaluated,
        missingValueEncoding: "thirteen empty CSV fields",
        evaluatedRows: rows.filter((row) => row.lanyonEvaluation === lanyonEvaluated).length,
        notEvaluatedRows: rows
          .filter((row) => row.lanyonEvaluation === lanyonNotEvaluated)
          .map((row) => row.name),
        outputPolicy: "report both reconstructed numerical fluxes; do not average, select, or require equality",
        finiteWordsRequiredForEvaluatedRows: true,
      },
    },
    parameters: {
      verifiedRealGamma: "7/5 (exact)",
      fixedAlpha: "7/4 (exact real and exactly representable binary64)",
      lanyonGasGamma: {
        cExpression: "7.0 / 5.0",
        binary64Bits: "3ff6666666666666",
        relationToVerifiedRealGamma: "binary64 approximation; not the exact rational 7/5",
      },
      lanyonAlpha: "dynamic per interface",
    },
    compilerContract: {
      executable: "cc",
      language: "C11",
      flags: strictCFlags,
      mirrorLinkFlags: linkFlags,
      lanyonLinkFlags: linkFlags,
      floatingPointEnvironment: "IEC 60559 binary64, FE_TONEAREST",
      platformChecks: [
        "__STDC_IEC_559__ is defined",
        "CHAR_BIT == 8 and uint64_t/double are 8 bytes",
        "FLT_RADIX == 2 and binary64 exponent/significand limits match",
        "FLT_EVAL_METHOD == 0",
        "double word layout maps 1.0 to 3ff0000000000000",
        "fesetround(FE_TONEAREST) succeeds and fegetround confirms it",
      ],
      compilerBinaryIdentity: null,
      compilerBinaryIdentityReason:
        "host compiler is not a repository input; source identities, flags, and exact output words are pinned",
    },
    cSources: {
      fixedAlphaMirror: fileIdentity(mirrorSourcePath),
      lanyonDriver: fileIdentity(lanyonDriverPath),
      fixtureReadme: fileIdentity(fixtureReadmePath),
      lanyonUpstream: {
        repository: lanyonRepository,
        commit: lanyonCommit,
        source: {
          ...fileIdentity(lanyonSourcePath),
          gitBlobSha1: lanyonSourceGitBlob,
        },
        license: {
          ...fileIdentity(lanyonLicensePath),
          gitBlobSha1: lanyonLicenseGitBlob,
        },
        metadata: fileIdentity(lanyonMetadataPath),
        metadataValue: upstreamMetadata,
      },
    },
    lanyonOutputColumns: lanyonColumns,
    generatorIdentity: identity,
    generatorRevision: `sha256:${identity.sha256}`,
    csvFile: path.basename(csvPath),
    csvByteLength: Buffer.byteLength(csv, "utf8"),
    csvSha256: sha256(Buffer.from(csv, "utf8")),
    encoding: "UTF-8",
    lineEndings: "LF",
  };
  return `${JSON.stringify(value, null, 2)}\n`;
}

async function buildDataset() {
  const interfaceBuilt = await buildInterfaceDataset();
  checkPublishedInterfaceDataset(interfaceBuilt);
  const upstreamMetadata = readUpstreamMetadata();
  validatePinnedUpstream(upstreamMetadata);
  requireEqual("interface row count", interfaceBuilt.rows.length, frozenRows.length);
  const compiled = compileComparators();
  let mirrorInvocationCount = 0;
  let lanyonInvocationCount = 0;
  const rows = interfaceBuilt.rows.map((verified, index) => {
    const frozen = frozenRows[index];
    requireEqual(`row ${index} case`, verified.name, frozen.name);
    requireEqual(`row ${verified.name} inputs`, JSON.stringify(verified.inputs), JSON.stringify(frozen.words));

    mirrorInvocationCount += 1;
    const mirror = parseMirrorOutput(
      verified.name,
      runText([compiled.mirrorExecutable, ...verified.inputs]),
    );
    requireEqual(`${verified.name} mirror status`, mirror.status, verified.status);
    requireEqual(
      `${verified.name} mirror outputs`,
      JSON.stringify(mirror.outputs),
      JSON.stringify(verified.outputs),
    );

    let lanyonEvaluation = lanyonNotEvaluated;
    let lanyonWords = Array(13).fill("");
    if (verified.status === 0n) {
      lanyonInvocationCount += 1;
      lanyonEvaluation = lanyonEvaluated;
      lanyonWords = parseLanyonOutput(
        verified.name,
        runText([compiled.lanyonExecutable, ...verified.inputs]),
      );
      for (const [wordIndex, word] of lanyonWords.entries()) {
        if (!isFiniteBinary64Word(word)) {
          throw new Error(`${verified.name}: Lanyon word ${wordIndex} is not finite binary64`);
        }
      }
    }

    return {
      name: verified.name,
      inputs: [...verified.inputs],
      verifiedStatus: verified.status,
      verifiedOutputs: [...verified.outputs],
      mirrorStatus: mirror.status,
      mirrorOutputs: [...mirror.outputs],
      mirrorRelation,
      lanyonEvaluation,
      lanyonWords,
    };
  });
  requireEqual("fixed-alpha mirror invocation count", mirrorInvocationCount, 8);
  requireEqual("Lanyon invocation count", lanyonInvocationCount, 7);

  const csv = csvText(rows);
  if (csv.includes("\r")) {
    throw new Error("generated C comparison CSV contains a non-LF line ending");
  }
  const identity = generatorIdentity();
  const manifest = manifestText(interfaceBuilt, rows, csv, identity, upstreamMetadata);
  return {
    compiled,
    csv,
    identity,
    interfaceBuilt,
    lanyonInvocationCount,
    manifest,
    mirrorInvocationCount,
    rows,
    upstreamMetadata,
  };
}

function requireExactFile(file, expected) {
  let actual;
  try {
    actual = fs.readFileSync(file, "utf8");
  } catch (error) {
    throw new Error(`could not read generated file ${relativeFile(file)}: ${error.message}`);
  }
  if (actual !== expected) {
    throw new Error(
      `${relativeFile(file)} is stale; run node tools/euler-rusanov-c-compare.js write`,
    );
  }
}

function checkPublishedDataset(built) {
  requireExactFile(csvPath, built.csv);
  requireExactFile(dataManifestPath, built.manifest);
}

function writePublishedDataset(built) {
  fs.mkdirSync(outputDirectory, { recursive: true });
  for (const [file, contents] of [
    [csvPath, built.csv],
    [dataManifestPath, built.manifest],
  ]) {
    if (!fs.existsSync(file) || fs.readFileSync(file, "utf8") !== contents) {
      const temporary = path.join(
        path.dirname(file),
        `.${path.basename(file)}.euler-rusanov-c-${process.pid}-${crypto.randomUUID()}.tmp`,
      );
      fs.writeFileSync(temporary, contents, { encoding: "utf8", flag: "wx", mode: 0o644 });
      fs.renameSync(temporary, file);
    }
  }
}

async function main(argv) {
  const command = argv[0] || "check";
  if (argv.length > 1 || (command !== "write" && command !== "check")) {
    throw new Error("usage: node tools/euler-rusanov-c-compare.js [write|check]");
  }
  const built = await buildDataset();
  if (command === "write") {
    writePublishedDataset(built);
    process.stdout.write(
      `wrote ${dataset}: ${built.mirrorInvocationCount}/8 bit-exact mirror rows, ` +
      `${built.lanyonInvocationCount} finite Lanyon rows, CSV ${sha256(Buffer.from(built.csv, "utf8"))}\n`,
    );
    return;
  }
  checkPublishedDataset(built);
  process.stdout.write(
    `checked ${dataset}: 8/8 fixed-alpha mirror rows, ` +
    "7 finite distinct-method Lanyon rows, CSV, and regression manifest\n",
  );
}

module.exports = {
  buildDataset,
  checkPublishedDataset,
  compileComparators,
  csvPath,
  dataManifestPath,
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
  writePublishedDataset,
};

if (require.main === module) {
  main(process.argv.slice(2)).catch((error) => {
    process.stderr.write(`${error.message}\n`);
    process.exitCode = 1;
  });
}
