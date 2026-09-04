#!/usr/bin/env node
"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const {
  loadArtifactRegistry,
  sha256,
  validateArtifactManifest,
} = require("./artifact-manifest");
const { callI64Slots } = require("./wasmtime-host");

const repoRoot = path.resolve(__dirname, "..");
const outputDirectory = path.join(repoRoot, "data", "euler-rusanov-interface-v1");
const csvPath = path.join(outputDirectory, "euler-rusanov-interface-v1.csv");
const dataManifestPath = path.join(outputDirectory, "manifest.json");

const dataset = "euler-rusanov-interface-v1";
const artifactCase = "euler_rusanov";
const artifactSha256 = "145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546";
const artifactByteLength = 1808;
const exportedFunction = "rusanovFluxCheckedBits";
const formalProofModule = "Project.EulerRusanov.InterfaceData";
const formalProofTheorem = "Project.EulerRusanov.InterfaceData.artifact_interfaceV1";
const generatorIdentityScheme = "leanexe-euler-rusanov-interface-generator-v1";
const generatorSourcePaths = Object.freeze([
  "tools/euler-rusanov-interface.js",
  "tools/wasmtime-host.js",
]);
const schema = [
  "case",
  "rho_l_bits",
  "u_l_bits",
  "p_l_bits",
  "rho_r_bits",
  "u_r_bits",
  "p_r_bits",
  "status_u64",
  "mass_bits",
  "momentum_bits",
  "energy_bits",
];

const bits = Object.freeze({
  zero: "0000000000000000",
  one: "3ff0000000000000",
  half: "3fe0000000000000",
  quarter: "3fd0000000000000",
  eighth: "3fc0000000000000",
  sixteenth: "3fb0000000000000",
  tenth: "3fb999999999999a",
  negativeHalf: "bfe0000000000000",
  quietNaN: "7ff8000000000000",
});

const states = Object.freeze({
  left: Object.freeze([bits.one, bits.zero, bits.one]),
  right: Object.freeze([bits.eighth, bits.zero, bits.tenth]),
  middle: Object.freeze([bits.half, bits.quarter, bits.quarter]),
  bottom: Object.freeze([bits.eighth, bits.negativeHalf, bits.sixteenth]),
  top: Object.freeze([bits.one, bits.half, bits.one]),
});

const frozenRows = Object.freeze([
  Object.freeze({ name: "sod_ll", words: Object.freeze([...states.left, ...states.left]) }),
  Object.freeze({ name: "sod_rr", words: Object.freeze([...states.right, ...states.right]) }),
  Object.freeze({ name: "sod_lr", words: Object.freeze([...states.left, ...states.right]) }),
  Object.freeze({ name: "sod_rl", words: Object.freeze([...states.right, ...states.left]) }),
  Object.freeze({
    name: "moving_consistency",
    words: Object.freeze([...states.middle, ...states.middle]),
  }),
  Object.freeze({
    name: "guard_min_to_max",
    words: Object.freeze([...states.bottom, ...states.top]),
  }),
  Object.freeze({
    name: "guard_max_to_min",
    words: Object.freeze([...states.top, ...states.bottom]),
  }),
  Object.freeze({
    name: "nan_rejected",
    words: Object.freeze([bits.quietNaN, bits.zero, bits.one, ...states.right]),
  }),
]);

function requireEqual(label, actual, expected) {
  if (actual !== expected) {
    throw new Error(`${label}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

function loadRegisteredArtifact() {
  const { registry } = loadArtifactRegistry(repoRoot);
  const matches = registry.artifacts.filter((entry) => entry.case === artifactCase);
  requireEqual(`${artifactCase} registry entry count`, matches.length, 1);
  const entry = matches[0];
  requireEqual(`${artifactCase} registry SHA-256`, entry.sha256, artifactSha256);

  const canonicalManifest = `${artifactCase}/${artifactSha256}/manifest.json`;
  requireEqual(`${artifactCase} registry manifest`, entry.manifest, canonicalManifest);
  const validated = validateArtifactManifest(repoRoot, entry);
  const { binaryPath: wasmPath, manifest, manifestPath } = validated;
  requireEqual("validated artifact manifest case", manifest.case, artifactCase);
  requireEqual("validated artifact manifest SHA-256", manifest.sha256, artifactSha256);
  requireEqual("validated artifact manifest byte length", manifest.byteLength, artifactByteLength);
  requireEqual("artifact manifest host assumptions", JSON.stringify(manifest.hostAssumptions), "[]");

  return {
    entry,
    manifest,
    manifestPath,
    wasmPath,
  };
}

function generatorIdentity() {
  const sources = [...generatorSourcePaths].sort().map((relative) => {
    const bytes = fs.readFileSync(path.join(repoRoot, ...relative.split("/")));
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

function parseWord(word) {
  if (!/^[0-9a-f]{16}$/.test(word)) {
    throw new Error(`invalid frozen binary64 word ${JSON.stringify(word)}`);
  }
  return BigInt(`0x${word}`);
}

function formatWord(value) {
  return BigInt.asUintN(64, value).toString(16).padStart(16, "0");
}

function csvText(rows) {
  const lines = [schema.join(",")];
  for (const row of rows) {
    lines.push([
      row.name,
      ...row.inputs,
      row.status.toString(10),
      ...row.outputs,
    ].join(","));
  }
  return `${lines.join("\n")}\n`;
}

function manifestText(artifact, csv, identity) {
  const manifestRelative = path.relative(repoRoot, artifact.manifestPath).split(path.sep).join("/");
  const rawWordColumns = schema.filter((column) => column.endsWith("_bits"));
  const value = {
    schemaVersion: 1,
    dataset,
    csvSchema: schema,
    rowCount: frozenRows.length,
    rowOrder: frozenRows.map((row) => row.name),
    wordEncoding: {
      columns: rawWordColumns,
      format: "lowercase fixed-width 16-digit hexadecimal without 0x",
      semantics: "raw IEEE 754 binary64 word",
    },
    statusEncoding: {
      column: "status_u64",
      format: "minimal unsigned base-10 UInt64",
      accepted: "0",
      rejected: "1",
    },
    registryEntry: artifactCase,
    artifactManifest: manifestRelative,
    wasmSha256: artifactSha256,
    wasmByteLength: artifactByteLength,
    exportedFunction,
    parameters: {
      gamma: "7/5",
      alpha: "7/4",
    },
    roundingSemantics: "IEEE 754 binary64 round-to-nearest, ties-to-even",
    formalProofModule,
    formalProofTheorem,
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
  const artifact = loadRegisteredArtifact();
  let invocationCount = 0;
  const rows = frozenRows.map((row) => {
    invocationCount += 1;
    const result = callI64Slots(
      artifact.wasmPath,
      exportedFunction,
      4,
      row.words.map(parseWord),
    );
    return {
      name: row.name,
      inputs: [...row.words],
      status: BigInt.asUintN(64, result[0]),
      outputs: result.slice(1).map(formatWord),
    };
  });
  requireEqual("WASM invocation count", invocationCount, frozenRows.length);

  const csv = csvText(rows);
  if (csv.includes("\r")) {
    throw new Error("generated CSV contains a non-LF line ending");
  }
  const identity = generatorIdentity();
  const manifest = manifestText(artifact, csv, identity);
  return { artifact, csv, invocationCount, manifest, rows };
}

function requireExactFile(file, expected) {
  let actual;
  try {
    actual = fs.readFileSync(file, "utf8");
  } catch (error) {
    throw new Error(`could not read generated file ${path.relative(repoRoot, file)}: ${error.message}`);
  }
  if (actual !== expected) {
    throw new Error(
      `${path.relative(repoRoot, file)} is stale; run ` +
      "node tools/euler-rusanov-interface.js write",
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
        `.${path.basename(file)}.euler-rusanov-${process.pid}-${crypto.randomUUID()}.tmp`,
      );
      fs.writeFileSync(temporary, contents, { encoding: "utf8", flag: "wx", mode: 0o644 });
      fs.renameSync(temporary, file);
    }
  }
}

async function main(argv) {
  const command = argv[0] || "check";
  if (argv.length > 1 || (command !== "write" && command !== "check")) {
    throw new Error("usage: node tools/euler-rusanov-interface.js [write|check]");
  }
  const built = await buildDataset();
  if (command === "write") {
    writePublishedDataset(built);
    process.stdout.write(
      `wrote ${dataset}: ${built.rows.length} rows, ` +
      `WASM ${artifactSha256}, CSV ${sha256(Buffer.from(built.csv, "utf8"))}\n`,
    );
    return;
  }
  checkPublishedDataset(built);
  process.stdout.write(
    `checked ${dataset}: registered WASM identity, ${built.invocationCount} calls, CSV, and manifest\n`,
  );
}

module.exports = {
  artifactByteLength,
  artifactCase,
  artifactSha256,
  buildDataset,
  checkPublishedDataset,
  csvPath,
  dataManifestPath,
  dataset,
  exportedFunction,
  formalProofModule,
  formalProofTheorem,
  frozenRows,
  generatorIdentity,
  generatorIdentityScheme,
  generatorSourcePaths,
  loadRegisteredArtifact,
  schema,
  sha256,
  writePublishedDataset,
};

if (require.main === module) {
  main(process.argv.slice(2)).catch((error) => {
    process.stderr.write(`${error.message}\n`);
    process.exitCode = 1;
  });
}
