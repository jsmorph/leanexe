#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const {
  artifactByteLength,
  artifactCase,
  artifactSha256,
  buildDataset,
  checkPublishedDataset,
  dataset,
  exportedFunction,
  formalProofModule,
  formalProofTheorem,
  generatorIdentity,
  generatorIdentityScheme,
  generatorSourcePaths,
  schema,
  sha256,
} = require("../tools/euler-rusanov-interface");
const {
  maxUInt64,
  parseI64SlotsOutput,
} = require("../tools/wasmtime-host");

const expectedCsv = [
  "case,rho_l_bits,u_l_bits,p_l_bits,rho_r_bits,u_r_bits,p_r_bits,status_u64,mass_bits,momentum_bits,energy_bits",
  "sod_ll,3ff0000000000000,0000000000000000,3ff0000000000000,3ff0000000000000,0000000000000000,3ff0000000000000,0,0000000000000000,3ff0000000000000,0000000000000000",
  "sod_rr,3fc0000000000000,0000000000000000,3fb999999999999a,3fc0000000000000,0000000000000000,3fb999999999999a,0,0000000000000000,3fb999999999999a,0000000000000000",
  "sod_lr,3ff0000000000000,0000000000000000,3ff0000000000000,3fc0000000000000,0000000000000000,3fb999999999999a,0,3fe8800000000000,3fe199999999999a,3fff800000000000",
  "sod_rl,3fc0000000000000,0000000000000000,3fb999999999999a,3ff0000000000000,0000000000000000,3ff0000000000000,0,bfe8800000000000,3fe199999999999a,bfff800000000000",
  "moving_consistency,3fe0000000000000,3fd0000000000000,3fd0000000000000,3fe0000000000000,3fd0000000000000,3fd0000000000000,0,3fc0000000000000,3fd2000000000000,3fcc800000000000",
  "guard_min_to_max,3fc0000000000000,bfe0000000000000,3fb0000000000000,3ff0000000000000,3fe0000000000000,3ff0000000000000,0,bfe1800000000000,3fc7000000000000,bff4c80000000000",
  "guard_max_to_min,3ff0000000000000,3fe0000000000000,3ff0000000000000,3fc0000000000000,bfe0000000000000,3fb0000000000000,0,3fef800000000000,3ff2a00000000000,4007f40000000000",
  "nan_rejected,7ff8000000000000,0000000000000000,3ff0000000000000,3fc0000000000000,0000000000000000,3fb999999999999a,1,0000000000000000,0000000000000000,0000000000000000",
  "",
].join("\n");

function requireEqual(label, actual, expected) {
  if (actual !== expected) {
    throw new Error(`${label}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

async function main() {
  const built = await buildDataset();
  checkPublishedDataset(built);
  requireEqual("dataset identifier", dataset, "euler-rusanov-interface-v1");
  requireEqual("registry entry", artifactCase, "euler_rusanov");
  requireEqual(
    "frozen artifact SHA-256",
    artifactSha256,
    "145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546",
  );
  requireEqual("frozen artifact byte length", artifactByteLength, 1808);
  requireEqual("exported function", exportedFunction, "rusanovFluxCheckedBits");
  requireEqual(
    "formal proof module",
    formalProofModule,
    "Project.EulerRusanov.InterfaceData",
  );
  requireEqual(
    "formal proof theorem",
    formalProofTheorem,
    "Project.EulerRusanov.InterfaceData.artifact_interfaceV1",
  );
  requireEqual("WASM invocation count", built.invocationCount, 8);
  requireEqual("CSV contents", built.csv, expectedCsv);
  requireEqual("CSV carriage-return count", (built.csv.match(/\r/g) || []).length, 0);

  const lines = built.csv.trimEnd().split("\n");
  requireEqual("CSV row count", lines.length, 9);
  requireEqual("CSV schema", lines[0], schema.join(","));
  for (const [index, line] of lines.slice(1).entries()) {
    const fields = line.split(",");
    requireEqual(`row ${index + 1} field count`, fields.length, schema.length);
    for (const fieldIndex of [1, 2, 3, 4, 5, 6, 8, 9, 10]) {
      if (!/^[0-9a-f]{16}$/.test(fields[fieldIndex])) {
        throw new Error(`row ${index + 1} contains a noncanonical raw word`);
      }
    }
    if (!/^[01]$/.test(fields[7])) {
      throw new Error(`row ${index + 1} contains a noncanonical status`);
    }
  }

  const manifest = JSON.parse(built.manifest);
  requireEqual("data manifest schema version", manifest.schemaVersion, 1);
  requireEqual("data manifest row count", manifest.rowCount, 8);
  requireEqual(
    "data manifest row order",
    JSON.stringify(manifest.rowOrder),
    JSON.stringify([
      "sod_ll",
      "sod_rr",
      "sod_lr",
      "sod_rl",
      "moving_consistency",
      "guard_min_to_max",
      "guard_max_to_min",
      "nan_rejected",
    ]),
  );
  requireEqual(
    "data manifest word format",
    manifest.wordEncoding.format,
    "lowercase fixed-width 16-digit hexadecimal without 0x",
  );
  requireEqual("data manifest status column", manifest.statusEncoding.column, "status_u64");
  requireEqual("data manifest registry entry", manifest.registryEntry, artifactCase);
  requireEqual("data manifest WASM SHA-256", manifest.wasmSha256, artifactSha256);
  requireEqual("data manifest export", manifest.exportedFunction, exportedFunction);
  requireEqual("data manifest gamma", manifest.parameters.gamma, "7/5");
  requireEqual("data manifest alpha", manifest.parameters.alpha, "7/4");
  requireEqual("data manifest proof module", manifest.formalProofModule, formalProofModule);
  requireEqual("data manifest proof theorem", manifest.formalProofTheorem, formalProofTheorem);
  requireEqual("data manifest line endings", manifest.lineEndings, "LF");
  requireEqual(
    "data manifest CSV byte length",
    manifest.csvByteLength,
    Buffer.byteLength(expectedCsv, "utf8"),
  );
  requireEqual(
    "data manifest CSV digest",
    manifest.csvSha256,
    sha256(Buffer.from(expectedCsv, "utf8")),
  );
  const identity = generatorIdentity();
  requireEqual("generator identity scheme", identity.scheme, generatorIdentityScheme);
  requireEqual(
    "generator source path order",
    JSON.stringify(generatorSourcePaths),
    JSON.stringify([...generatorSourcePaths].sort()),
  );
  requireEqual(
    "data manifest generator identity",
    JSON.stringify(manifest.generatorIdentity),
    JSON.stringify(identity),
  );
  requireEqual("data manifest generator revision", manifest.generatorRevision, `sha256:${identity.sha256}`);

  requireEqual(
    "maximum external UInt64",
    parseI64SlotsOutput("rangeProbe", 1, `${maxUInt64}\n`)[0],
    maxUInt64,
  );
  let rejectedOverflow = false;
  try {
    parseI64SlotsOutput("rangeProbe", 1, `${maxUInt64 + 1n}\n`);
  } catch (error) {
    rejectedOverflow = error.message.includes("outside UInt64");
  }
  requireEqual("external UInt64 overflow rejection", rejectedOverflow, true);
  const publishedManifest = fs.readFileSync(
    require("../tools/euler-rusanov-interface").dataManifestPath,
    "utf8",
  );
  requireEqual("published data manifest", publishedManifest, built.manifest);

  process.stdout.write(
    "checked euler-rusanov-interface-v1 registry identity, eight exact WASM rows, LF CSV, and data manifest\n",
  );
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exitCode = 1;
});
