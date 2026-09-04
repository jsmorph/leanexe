#!/usr/bin/env node
"use strict";

const childProcess = require("node:child_process");
const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const { expectedTalosRevision } = require("./artifact-manifest");
const { verifierSourceSha256 } = require("./artifact-source");

const repoRoot = path.resolve(__dirname, "..");
const proofRoot = path.join(repoRoot, "proofs", "talos", "lean");
const projectRoot = path.join(proofRoot, "Project");
const generatedRoot = path.join(repoRoot, "proofs", "talos", ".generated");
const artifactRoot = path.join(repoRoot, "proofs", "artifacts");
const casesPath = path.join(repoRoot, "proofs", "talos", "cases.json");
const leanrun = path.join(repoRoot, "tools", "leanrun");
const dumpRaw = path.join(projectRoot, "Artifact", "Binary", "DumpRaw.lean");
const dumpRawTarget = "Project.Artifact.Binary.DumpRaw";

function fail(message) {
  throw new Error(message);
}

function digest(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function textOutput(file, content) {
  if (!content.endsWith("\n")) content += "\n";
  return { file, bytes: Buffer.from(content), immutable: false };
}

function binaryOutput(file, bytes) {
  return { file, bytes, immutable: true };
}

function applyOutputs(outputs) {
  const destinations = new Set();
  const changed = [];
  for (const output of outputs) {
    if (destinations.has(output.file)) fail(`duplicate migration output: ${output.file}`);
    destinations.add(output.file);
    let existing = null;
    try {
      existing = fs.readFileSync(output.file);
    } catch (error) {
      if (error.code !== "ENOENT") throw error;
    }
    if (existing && existing.equals(output.bytes)) continue;
    if (existing && output.immutable) fail(`frozen file differs: ${output.file}`);
    changed.push({ ...output, existed: existing !== null });
  }

  const nonce = `${process.pid}-${Date.now()}`;
  const prepared = [];
  try {
    for (const [index, output] of changed.entries()) {
      fs.mkdirSync(path.dirname(output.file), { recursive: true });
      const temporary = `${output.file}.tmp-${nonce}-${index}`;
      fs.writeFileSync(temporary, output.bytes, { flag: "wx" });
      prepared.push({
        ...output,
        temporary,
        backup: `${output.file}.bak-${nonce}-${index}`,
        installed: false,
      });
    }

    for (const output of prepared) {
      if (output.existed) fs.renameSync(output.file, output.backup);
      try {
        fs.renameSync(output.temporary, output.file);
        output.installed = true;
      } catch (error) {
        if (output.existed) fs.renameSync(output.backup, output.file);
        throw error;
      }
    }
  } catch (error) {
    const cleanupErrors = [];
    for (const output of [...prepared].reverse()) {
      try {
        if (output.installed) fs.rmSync(output.file, { force: true });
        if (fs.existsSync(output.backup)) fs.renameSync(output.backup, output.file);
        fs.rmSync(output.temporary, { force: true });
      } catch (cleanupError) {
        cleanupErrors.push(cleanupError);
      }
    }
    if (cleanupErrors.length > 0) {
      throw new AggregateError([error, ...cleanupErrors], "artifact migration rollback failed");
    }
    throw error;
  }

  for (const output of prepared) fs.rmSync(output.backup, { force: true });
}

function buildDumpRaw(spawnSync = childProcess.spawnSync) {
  const result = spawnSync(leanrun, [
    "--timeout", "15m",
    "lake", "-d", proofRoot, "build", dumpRawTarget,
  ], {
    cwd: repoRoot,
    env: process.env,
    stdio: "inherit",
  });
  if (result.error) {
    fail(`raw-module decoder build failed: ${result.error.message}`);
  }
  if (result.signal) {
    fail(`raw-module decoder build terminated by ${result.signal}`);
  }
  if (result.status !== 0) {
    fail(`raw-module decoder build failed with exit status ${result.status}`);
  }
}

function runDumpRaw(wasm) {
  const result = childProcess.spawnSync(leanrun, [
    "--timeout", "5m",
    "lake", "-d", proofRoot, "env", "lean", "--run", dumpRaw, wasm,
  ], {
    cwd: repoRoot,
    encoding: "utf8",
    env: process.env,
    maxBuffer: 64 * 1024 * 1024,
  });
  const relayOutput = () => {
    if (result.stdout) process.stderr.write(result.stdout);
    if (result.stderr) process.stderr.write(result.stderr);
  };
  if (result.error) {
    relayOutput();
    fail(`raw-module decode failed: ${result.error.message}`);
  }
  if (result.signal) {
    relayOutput();
    fail(`raw-module decode terminated by ${result.signal}`);
  }
  if (result.status !== 0) {
    relayOutput();
    fail(`raw-module decode failed with exit status ${result.status}`);
  }
  const output = result.stdout.trim();
  if (!output.startsWith("{") || !output.endsWith("}")) {
    fail(`raw-module decoder produced unexpected output for ${wasm}`);
  }
  return output;
}

function formatBytes(bytes) {
  const values = [...bytes];
  const lines = [];
  for (let index = 0; index < values.length; index += 20) {
    lines.push(`    ${values.slice(index, index + 20).join(", ")}`);
  }
  return lines.join(",\n");
}

function typeIndices(raw) {
  const match = raw.match(/functionTypeIndices := \[([^\]]*)\]/s);
  if (!match) fail("raw module lacks functionTypeIndices");
  if (match[1].trim() === "") return [];
  return match[1].split(",").map((value) => {
    const parsed = Number(value.trim());
    if (!Number.isSafeInteger(parsed) || parsed < 0) {
      fail(`invalid function type index: ${value}`);
    }
    return parsed;
  });
}

function functionCount(item) {
  const program = fs.readFileSync(
    path.join(projectRoot, item.leanModule, "Program.lean"),
    "utf8",
  );
  const indices = [...program.matchAll(/^def func([0-9]+)Def : Wasm\.Function :=/gm)]
    .map((match) => Number(match[1]));
  if (indices.length === 0) fail(`${item.name}: generated program has no functions`);
  for (let index = 0; index < indices.length; index += 1) {
    if (indices[index] !== index) fail(`${item.name}: function definitions are not contiguous`);
  }
  return indices.length;
}

function bytesModule(item, sha256, bytes) {
  return `import Project.Artifact.Binary.Translate

set_option maxRecDepth 1048576

namespace Project.${item.leanModule}.Artifact

def sha256 : String :=
  "${sha256}"

def artifactBytes : ByteArray :=
  [
${formatBytes(bytes)}
  ].map UInt8.ofNat |>.toByteArray

theorem artifactBytes_size : artifactBytes.size = ${bytes.length} := by
  native_decide

end Project.${item.leanModule}.Artifact`;
}

function cacheModule(item, raw) {
  return `import Project.Artifact.Binary.Syntax

namespace Project.${item.leanModule}.Artifact.Cache

def raw : Wasm.Binary.RawModule :=
${raw}

end Project.${item.leanModule}.Artifact.Cache`;
}

function decodedModule(item) {
  return `import Project.${item.leanModule}.ArtifactBytes
import Project.Artifact.Binary.Decode

set_option maxRecDepth 1048576

namespace Project.${item.leanModule}.Artifact

open Wasm.Binary

def decodedRaw? : Option RawModule :=
  (decode artifactBytes).toOption

theorem decodedRaw_isSome : decodedRaw?.isSome = true := by
  native_decide

def decodedRaw : RawModule :=
  decodedRaw?.getD default

theorem decode_eq_decodedRaw : decode artifactBytes = .ok decodedRaw := by
  cases hdecode : decode artifactBytes with
  | error error =>
      have h := decodedRaw_isSome
      unfold decodedRaw? at h
      rw [hdecode] at h
      change (none : Option RawModule).isSome = true at h
      cases h
  | ok raw =>
      unfold decodedRaw decodedRaw?
      rw [hdecode]
      rfl

end Project.${item.leanModule}.Artifact`;
}

function rawCacheModule(item) {
  return `import Project.${item.leanModule}.ArtifactDecoded
import Project.${item.leanModule}.ArtifactCache
import Project.Artifact.Binary.Equality

namespace Project.${item.leanModule}.Artifact

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end Project.${item.leanModule}.Artifact`;
}

function decodeModule(item) {
  return `import Project.${item.leanModule}.ArtifactDecoded
import Project.${item.leanModule}.ArtifactRawCache

namespace Project.${item.leanModule}.Artifact

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end Project.${item.leanModule}.Artifact`;
}

function validationModule(item) {
  return `import Project.${item.leanModule}.ArtifactDecode
import Project.Artifact.Binary.Evidence

namespace Project.${item.leanModule}.Artifact

open Wasm.Binary

def cacheValidationSucceeded : Bool :=
  (validate Cache.raw).toOption.isSome

theorem cache_validation_test : cacheValidationSucceeded = true := by
  native_decide

theorem cache_validation_exists :
    ∃ validated, validate Cache.raw = .ok validated := by
  exact ok_exists_of_toOption_isSome cache_validation_test

end Project.${item.leanModule}.Artifact`;
}

function translationModule(item, indices) {
  const functionTheorems = indices.map((typeIndex, index) => `theorem function${index}_eq :
    Translation.functionToTalos Cache.raw ${typeIndex} (Cache.raw.codes[${index}]!) =
      Project.${item.leanModule}.func${index}Def := by
  rfl`).join("\n\n");
  const left = indices.map((typeIndex, index) =>
    `     Translation.functionToTalos Cache.raw ${typeIndex} (Cache.raw.codes[${index}]!)`,
  ).join(",\n");
  const right = indices.map((_, index) => `Project.${item.leanModule}.func${index}Def`).join(", ");
  const rewrites = indices.map((_, index) => `function${index}_eq`).join(", ");
  return `import Project.${item.leanModule}.ArtifactValidation
import Project.${item.leanModule}.Program
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace Project.${item.leanModule}.Artifact

open Wasm
open Wasm.Binary

${functionTheorems}

theorem functions_eq : Translation.functions Cache.raw =
    Project.${item.leanModule}.«module».funcs := by
  change
    [
${left}
    ] =
    [${right}]
  rw [${rewrites}]

def executionCache : Wasm.Module :=
  Project.${item.leanModule}.«module»

theorem translation_cache_eq :
    Translation.module Cache.raw = executionCache := by
  unfold Translation.module executionCache
  rw [functions_eq]
  rfl

theorem artifact_correct_of (Property : Wasm.Module → Prop)
    (behavior : Property executionCache) :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Property validated.toTalos := by
  rcases cache_validation_exists with ⟨validated, hvalidate⟩
  have htranslation : validated.toTalos = executionCache := by
    rw [ValidatedModule.toTalos, Proof.validate_raw_eq hvalidate,
      translation_cache_eq]
  refine ⟨Cache.raw, validated, decode_eq_cache, hvalidate,
    Proof.validate_sound hvalidate, ?_⟩
  rw [htranslation]
  exact behavior

theorem artifact_module_eq_cache :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      validated.toTalos = executionCache := by
  exact artifact_correct_of (fun module_ => module_ = executionCache) rfl

end Project.${item.leanModule}.Artifact`;
}

function manifest(item, sha256, byteLength) {
  return {
    schemaVersion: 3,
    case: item.name,
    sha256,
    byteLength,
    binaryFormatVersion: 1,
    validationProfile: "leanexe-core-v1",
    artifactBytesModule: `Project.${item.leanModule}.ArtifactBytes`,
    artifactBytesDefinition: `Project.${item.leanModule}.Artifact.artifactBytes`,
    rawModuleDefinition: `Project.${item.leanModule}.Artifact.Cache.raw`,
    cachedProgramModule: `Project.${item.leanModule}.Program`,
    cachedProgramDefinition: `Project.${item.leanModule}.module`,
    specModule: item.specTarget,
    proofTarget: `Project.${item.leanModule}.ArtifactTranslation`,
    identityTheorem: `Project.${item.leanModule}.Artifact.decode_eq_cache`,
    decodeTheorem: "Wasm.Binary.Proof.decode_sound",
    validationTheorem: "Wasm.Binary.Proof.validate_sound",
    cacheEqualityTheorem: `Project.${item.leanModule}.Artifact.translation_cache_eq`,
    artifactCorrectnessTheorem:
      `Project.${item.leanModule}.Artifact.artifact_module_eq_cache`,
    behaviorTheorems: item.behaviorTheorems,
    leanToolchain: fs.readFileSync(path.join(repoRoot, "lean-toolchain"), "utf8").trim(),
    talosRevision: expectedTalosRevision(repoRoot),
    verifierSourceSha256: verifierSourceSha256(repoRoot),
    hostAssumptions: [],
  };
}

function migrate(item) {
  if (item.name === "gcd") return;
  const wasm = path.join(generatedRoot, item.name, "program.wasm");
  const bytes = fs.readFileSync(wasm);
  const sha256 = digest(bytes);
  const raw = runDumpRaw(wasm);
  const indices = typeIndices(raw);
  const count = functionCount(item);
  if (indices.length !== count) {
    fail(`${item.name}: ${indices.length} type indices for ${count} functions`);
  }
  const moduleRoot = path.join(projectRoot, item.leanModule);
  const outputs = [
    textOutput(path.join(moduleRoot, "ArtifactBytes.lean"), bytesModule(item, sha256, bytes)),
    textOutput(path.join(moduleRoot, "ArtifactCache.lean"), cacheModule(item, raw)),
    textOutput(path.join(moduleRoot, "ArtifactDecoded.lean"), decodedModule(item)),
    textOutput(path.join(moduleRoot, "ArtifactRawCache.lean"), rawCacheModule(item)),
    textOutput(path.join(moduleRoot, "ArtifactDecode.lean"), decodeModule(item)),
    textOutput(path.join(moduleRoot, "ArtifactValidation.lean"), validationModule(item)),
    textOutput(
      path.join(moduleRoot, "ArtifactTranslation.lean"),
      translationModule(item, indices),
    ),
  ];
  const packageRoot = path.join(artifactRoot, item.name, sha256);
  const manifestValue = manifest(item, sha256, bytes.length);
  outputs.push(
    textOutput(path.join(packageRoot, "manifest.json"), JSON.stringify(manifestValue, null, 2)),
    binaryOutput(path.join(packageRoot, "program.wasm"), bytes),
  );
  return {
    entry: {
      case: item.name,
      sha256,
      manifest: `${item.name}/${sha256}/manifest.json`,
      proofTarget: manifestValue.proofTarget,
    },
    outputs,
  };
}

function checkFileOutput(entries, cases) {
  const byName = new Map(cases.map((item) => [item.name, item]));
  const imports = entries.map((entry) =>
    `import Project.${byName.get(entry.case).leanModule}.ArtifactBytes`,
  ).join("\n");
  const arms = entries.map((entry) => {
    const item = byName.get(entry.case);
    return `  | "${entry.case}" => some Project.${item.leanModule}.Artifact.artifactBytes`;
  }).join("\n");
  return textOutput(path.join(projectRoot, "Artifact", "Binary", "CheckFile.lean"), `${imports}

private def artifactBytes : String → Option ByteArray
${arms}
  | _ => none

def main (args : List String) : IO UInt32 := do
  let rec check : List String → IO UInt32
  | [] => pure 0
  | caseName :: path :: rest => do
      let some expected := artifactBytes caseName
        | IO.eprintln s!"unregistered artifact case: {caseName}"
          return 2
      let found ← IO.FS.readBinFile path
      if found == expected then
        IO.println s!"embedded bytes matched {caseName}: {found.size} bytes"
        check rest
      else
        IO.eprintln s!"embedded bytes differ for {caseName}: {path}"
        pure 1
  | _ => do
      IO.eprintln "usage: CheckFile (<case> <program.wasm>)+"
      pure 2
  check args`);
}

function main() {
  if (process.argv.length !== 4 || process.argv[2] !== "migrate") {
    fail("usage: artifact-migrate.js migrate <case | --all>");
  }
  const cases = JSON.parse(fs.readFileSync(casesPath, "utf8")).cases;
  const selected = process.argv[3] === "--all"
    ? cases.filter((item) => item.name !== "gcd")
    : cases.filter((item) => item.name === process.argv[3]);
  if (selected.length === 0) fail(`unknown or already hand-migrated case: ${process.argv[3]}`);
  const registryPath = path.join(artifactRoot, "registry.json");
  const registry = JSON.parse(fs.readFileSync(registryPath, "utf8"));
  const entries = new Map(registry.artifacts.map((entry) => [entry.case, entry]));
  buildDumpRaw();
  const outputs = [];
  for (const item of selected) {
    console.log(`Migrating artifact: ${item.name}`);
    const migrated = migrate(item);
    entries.set(item.name, migrated.entry);
    outputs.push(...migrated.outputs);
  }
  const ordered = cases.filter((item) => entries.has(item.name)).map((item) => entries.get(item.name));
  outputs.push(
    textOutput(registryPath, JSON.stringify({ version: 1, artifacts: ordered }, null, 2)),
    checkFileOutput(ordered, cases),
  );
  applyOutputs(outputs);
  console.log(`Artifact migration completed: ${selected.length} case(s)`);
}

if (require.main === module) {
  try {
    main();
  } catch (error) {
    console.error(`artifact-migrate.js: ${error.message}`);
    process.exitCode = 1;
  }
}

module.exports = {
  applyOutputs,
  binaryOutput,
  buildDumpRaw,
  textOutput,
};
