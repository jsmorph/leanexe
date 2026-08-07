"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");
const { expectedTalosRevision } = require("./artifact-manifest");
const { verifierSourceSha256 } = require("./artifact-source");
const {
  matchAnnotationDocument,
  validateAnnotationDocument,
  validateProofRecipePlan,
} = require("./leanexegen-annotations");
const { validateStage5Telemetry } = require("./leanexegen-telemetry");

const codexTaskSchemaVersion = 2;
const packageSchemaVersion = 5;
const supportedPackageSchemaVersions = new Set([3, 4, packageSchemaVersion]);
const caseNamePattern = /^[a-z][a-z0-9]*(?:_[a-z0-9]+)*$/;
const decimalPattern = /^(?:0|[1-9][0-9]*)$/;
const uint64Maximum = 18446744073709551615n;
const proofKitModules = Object.freeze([
  "Project.ProofKit.Annotation",
  "Project.ProofKit.Memory",
  "Project.ProofKit.Array",
  "Project.ProofKit.Allocation",
  "Project.ProofKit.FixedArrayAllocator",
  "Project.ProofKit.FixedArrayAllocatorWindow",
  "Project.ProofKit.FixedArrayEqNode",
  "Project.ProofKit.FixedArrayInput",
  "Project.ProofKit.FixedArrayLengthDispatch",
  "Project.ProofKit.FixedArrayLtNode",
  "Project.ProofKit.FixedArrayPairResult",
  "Project.ProofKit.FixedArrayResult",
  "Project.ProofKit.FixedArraySearch",
  "Project.ProofKit.FixedArraySearchTree",
  "Project.ProofKit.FixedArraySingleton",
  "Project.ProofKit.FixedArrayTraversalInput",
  "Project.ProofKit.Control",
]);
const proofKitRelativeFiles = Object.freeze([
  "proofs/talos/lean/Project/ProofKit/Annotation.lean",
  "proofs/talos/lean/Project/ProofKit/Memory.lean",
  "proofs/talos/lean/Project/ProofKit/Array.lean",
  "proofs/talos/lean/Project/ProofKit/Allocation.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayAllocator.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayAllocatorWindow.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayEqNode.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayInput.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayLengthDispatch.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayLtNode.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayPairResult.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayResult.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySearch.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySearchTree.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySingleton.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayTraversalInput.lean",
  "proofs/talos/lean/Project/ProofKit/Control.lean",
  "proofs/talos/lean/Project/ProofKit/README.md",
]);

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function exactKeys(value, keys, description) {
  if (value === null || typeof value !== "object" || Array.isArray(value)) {
    fail(`${description} must be an object`);
  }
  const found = Object.keys(value).sort();
  const expected = [...keys].sort();
  if (found.length !== expected.length ||
      found.some((key, index) => key !== expected[index])) {
    fail(`${description} must contain exactly: ${expected.join(", ")}`);
  }
}

function requireString(value, description) {
  if (typeof value !== "string" || value.trim() !== value || value.length === 0) {
    fail(`${description} must be a trimmed, nonempty string`);
  }
  return value;
}

function requireSource(value, description) {
  if (typeof value !== "string" || value.trim().length === 0 || value.includes("\0")) {
    fail(`${description} must be nonempty Lean source text without NUL bytes`);
  }
  return value;
}

function validateProofJournal(value, description = "proof journal") {
  const prose = typeof value === "string"
    ? value.split(/\r?\n/).filter((line) =>
      !/^\s{0,3}#{1,6}(?:\s|$)/.test(line)).join("\n").trim()
    : "";
  if (typeof value !== "string" || value.includes("\0") || prose.length === 0) {
    fail(`${description} must contain substantive text without NUL bytes`);
  }
  return value;
}

function requireStringArray(value, description, allowEmpty = true) {
  if (!Array.isArray(value) || (!allowEmpty && value.length === 0)) {
    fail(`${description} must be ${allowEmpty ? "an" : "a nonempty"} array`);
  }
  const result = value.map((item, index) =>
    requireString(item, `${description}[${index}]`));
  if (new Set(result).size !== result.length) fail(`${description} contains duplicates`);
  return result;
}

function snakeToPascal(name) {
  return name.split("_").map((part) =>
    `${part[0].toUpperCase()}${part.slice(1)}`).join("");
}

function makeJob(request) {
  const requestSha256 = sha256(Buffer.from(request));
  const caseName = `generated_r${requestSha256.slice(0, 16)}`;
  const leanModule = snakeToPascal(caseName);
  const prefix = `LeanExeGen.${leanModule}`;
  return {
    requestSha256,
    caseName,
    leanModule,
    namespace: prefix,
    sourceModule: `${prefix}.Source`,
    formalSpecModule: `${prefix}.FormalSpec`,
    expectedDefinition: `${prefix}.FormalSpec.expected`,
    formalSpecDefinition: `${prefix}.FormalSpec.ArtifactSpec`,
    formalSpecType: "Wasm.Module → Prop",
    sourceEntry: `${prefix}.Source.compute`,
    exportName: "compute",
    programModule: `${prefix}.Program`,
    behaviorModule: `${prefix}.Behavior`,
    behaviorTheorem: `${prefix}.Behavior.artifact_behavior`,
    artifactTarget: `${prefix}.ArtifactResult`,
  };
}

function moduleFile(moduleName) {
  return `${moduleName.split(".").join("/")}.lean`;
}

function imports(source) {
  return [...source.matchAll(/^import[ \t]+([A-Za-z_][A-Za-z0-9_.]*)[ \t]*(?:--.*)?$/gm)]
    .map((match) => match[1]);
}

function validateProofImports(job, modules) {
  const generatedPrefix = `${job.namespace}.`;
  for (const item of modules) {
    for (const imported of imports(item.source)) {
      const allowedDependency = imported === "CodeLib" ||
        imported.startsWith("CodeLib.") ||
        imported.startsWith("Init.") ||
        imported.startsWith("Std.") ||
        imported.startsWith("Mathlib.") ||
        imported === "Interpreter" ||
        imported.startsWith("Interpreter.");
      const allowedProofKit = proofKitModules.includes(imported);
      const allowedGenerated = imported.startsWith(generatedPrefix) &&
        imported !== job.sourceModule;
      if (!allowedDependency && !allowedProofKit && !allowedGenerated) {
        fail(`${item.module} imports unsupported proof dependency ${imported}`);
      }
    }
  }
}

function validateProgramImports(job, source) {
  if (imports(source).includes(job.formalSpecModule)) {
    fail(`${job.sourceModule} must not import ${job.formalSpecModule}`);
  }
}

function validateSamples(samples, allowEmpty) {
  if (!Array.isArray(samples) || (!allowEmpty && samples.length === 0)) {
    fail(`samples must be ${allowEmpty ? "an" : "a nonempty"} array`);
  }
  for (const [index, sample] of samples.entries()) {
    exactKeys(sample, ["input", "expectedOutput"], `samples[${index}]`);
    if (!Array.isArray(sample.input) || sample.input.length > 256) {
      fail(`samples[${index}].input must contain at most 256 UInt64 values`);
    }
    if (!Array.isArray(sample.expectedOutput) || sample.expectedOutput.length > 256) {
      fail(`samples[${index}].expectedOutput must contain at most 256 UInt64 values`);
    }
    for (const [field, values] of [
      ["input", sample.input],
      ["expectedOutput", sample.expectedOutput],
    ]) {
      for (const [valueIndex, value] of values.entries()) {
        if (typeof value !== "string" || !decimalPattern.test(value) ||
            BigInt(value) > uint64Maximum) {
          fail(`samples[${index}].${field}[${valueIndex}] must be a UInt64 decimal`);
        }
      }
    }
  }
  return samples;
}

function validateCodexTaskOutcome(response, task) {
  exactKeys(response, [
    "schemaVersion",
    "task",
    "outcome",
    "summary",
    "decisions",
    "questions",
    "problems",
    "source",
    "samples",
    "hostAssumptions",
  ], "Codex task outcome");
  if (response.schemaVersion !== codexTaskSchemaVersion) {
    fail(`Codex task schemaVersion must be ${codexTaskSchemaVersion}`);
  }
  if (response.task !== task) fail(`Codex task must be ${task}`);
  if (!["generated", "questions", "problems"].includes(response.outcome)) {
    fail("unsupported Codex task outcome");
  }
  requireString(response.summary, "summary");
  requireStringArray(response.decisions, "decisions");
  requireStringArray(response.questions, "questions");
  requireStringArray(response.problems, "problems");
  requireStringArray(response.hostAssumptions, "hostAssumptions");
  if (response.outcome === "generated") {
    requireSource(response.source, "source");
    if (response.questions.length !== 0 || response.problems.length !== 0) {
      fail("generated Codex outcome must have empty questions and problems");
    }
  } else {
    if (response.source !== "") fail("non-generated Codex outcome must have empty source");
    const selected = response.outcome === "questions" ? response.questions : response.problems;
    const other = response.outcome === "questions" ? response.problems : response.questions;
    if (selected.length === 0 || other.length !== 0) {
      fail(`${response.outcome} Codex outcome has inconsistent detail arrays`);
    }
    return response;
  }
  const programGenerated = task === "lean-program" && response.outcome === "generated";
  validateSamples(response.samples, !programGenerated);
  if (!programGenerated && response.samples.length !== 0) {
    fail(`${task} outcome must not contain samples`);
  }
  const formalGenerated = task === "formal-specification" && response.outcome === "generated";
  if (!formalGenerated && response.hostAssumptions.length !== 0) {
    fail(`${task} outcome must not contain host assumptions`);
  }
  return response;
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

function functionCount(program) {
  const indices = [...program.matchAll(/^def func([0-9]+)Def : Wasm\.Function :=/gm)]
    .map((match) => Number(match[1]));
  if (indices.length === 0) fail("Talos program has no functions");
  for (let index = 0; index < indices.length; index += 1) {
    if (indices[index] !== index) fail("Talos function definitions are not contiguous");
  }
  return indices.length;
}

function rewriteProgramNamespace(program, job) {
  const from = `Project.${job.leanModule}`;
  const occurrences = program.split(from).length - 1;
  if (occurrences === 0) fail(`Talos program does not declare namespace ${from}`);
  return program.split(from).join(job.namespace);
}

function programExportIndex(program, exportName) {
  const escaped = exportName.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const pattern = new RegExp(
    `\\{\\s*name := "${escaped}",\\s*funcIdx := ([0-9]+)\\s*\\}`,
    "g",
  );
  const matches = [...program.matchAll(pattern)];
  if (matches.length !== 1) {
    fail(`Talos program has ${matches.length} exports named ${exportName}; expected one`);
  }
  const index = Number(matches[0][1]);
  const count = functionCount(program);
  if (!Number.isSafeInteger(index) || index < 0 || index >= count) {
    fail(`Talos export ${exportName} has unsupported function index ${matches[0][1]}`);
  }
  return index;
}

function artifactSources(job, wasmBytes, raw, talosProgram) {
  const prefix = job.namespace;
  const artifact = `${prefix}.Artifact`;
  const indices = typeIndices(raw);
  const count = functionCount(talosProgram);
  if (indices.length !== count) {
    fail(`Talos module has ${indices.length} type indices for ${count} functions`);
  }
  const digest = sha256(wasmBytes);
  const functionTheorems = indices.map((typeIndex, index) => `theorem function${index}_eq :
    Translation.functionToTalos Cache.raw ${typeIndex} (Cache.raw.codes[${index}]!) =
      ${prefix}.func${index}Def := by
  rfl`).join("\n\n");
  const left = indices.map((typeIndex, index) =>
    `     Translation.functionToTalos Cache.raw ${typeIndex} (Cache.raw.codes[${index}]!)`)
    .join(",\n");
  const right = indices.map((_, index) => `${prefix}.func${index}Def`).join(", ");
  const rewrites = indices.map((_, index) => `function${index}_eq`).join(", ");
  const sources = new Map();
  sources.set(job.programModule, talosProgram);
  sources.set(`${prefix}.ArtifactBytes`, `import Project.Artifact.Binary.Translate

set_option maxRecDepth 1048576

namespace ${artifact}

def sha256 : String :=
  "${digest}"

def artifactBytes : ByteArray :=
  [
${formatBytes(wasmBytes)}
  ].map UInt8.ofNat |>.toByteArray

theorem artifactBytes_size : artifactBytes.size = ${wasmBytes.length} := by
  native_decide

end ${artifact}
`);
  sources.set(`${prefix}.ArtifactCache`, `import Project.Artifact.Binary.Syntax

namespace ${artifact}.Cache

def raw : Wasm.Binary.RawModule :=
${raw}

end ${artifact}.Cache
`);
  sources.set(`${prefix}.ArtifactDecoded`, `import ${prefix}.ArtifactBytes
import Project.Artifact.Binary.Decode

set_option maxRecDepth 1048576

namespace ${artifact}

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

end ${artifact}
`);
  sources.set(`${prefix}.ArtifactRawCache`, `import ${prefix}.ArtifactDecoded
import ${prefix}.ArtifactCache
import Project.Artifact.Binary.Equality

namespace ${artifact}

open Wasm.Binary

def decodedRawMatchesCache : Bool :=
  Equality.rawModuleEqual 16384 decodedRaw Cache.raw

theorem decodedRaw_cache_test : decodedRawMatchesCache = true := by
  native_decide

theorem decodedRaw_eq_cache : decodedRaw = Cache.raw := by
  exact Equality.rawModuleEqual_sound decodedRaw_cache_test

end ${artifact}
`);
  sources.set(`${prefix}.ArtifactDecode`, `import ${prefix}.ArtifactDecoded
import ${prefix}.ArtifactRawCache

namespace ${artifact}

open Wasm.Binary

theorem decode_eq_cache : decode artifactBytes = .ok Cache.raw := by
  rw [decode_eq_decodedRaw, decodedRaw_eq_cache]

end ${artifact}
`);
  sources.set(`${prefix}.ArtifactValidation`, `import ${prefix}.ArtifactDecode
import Project.Artifact.Binary.Evidence

namespace ${artifact}

open Wasm.Binary

def cacheValidationSucceeded : Bool :=
  (validate Cache.raw).toOption.isSome

theorem cache_validation_test : cacheValidationSucceeded = true := by
  native_decide

theorem cache_validation_exists :
    ∃ validated, validate Cache.raw = .ok validated := by
  exact ok_exists_of_toOption_isSome cache_validation_test

end ${artifact}
`);
  sources.set(`${prefix}.ArtifactTranslation`, `import ${prefix}.ArtifactValidation
import ${job.programModule}
import Project.Artifact.Binary.Proof.Translate
import Project.Artifact.Binary.Proof.Validate

set_option maxRecDepth 1048576

namespace ${artifact}

open Wasm
open Wasm.Binary

${functionTheorems}

theorem functions_eq : Translation.functions Cache.raw =
    ${prefix}.«module».funcs := by
  change
    [
${left}
    ] =
    [${right}]
  rw [${rewrites}]

def executionCache : Wasm.Module :=
  ${prefix}.«module»

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

end ${artifact}
`);
  sources.set(`${prefix}.ArtifactResult`, `import ${prefix}.ArtifactTranslation
import ${job.formalSpecModule}
import ${job.behaviorModule}

namespace ${artifact}

open Wasm.Binary

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      ${job.formalSpecDefinition} validated.toTalos := by
  apply artifact_correct_of ${job.formalSpecDefinition}
  simpa [executionCache] using ${job.behaviorTheorem}

end ${artifact}
`);
  sources.set(`${prefix}.CheckFile`, `import ${prefix}.ArtifactBytes

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: CheckFile <program.wasm>"
      return 2
  let found ← IO.FS.readBinFile file
  if found == ${artifact}.artifactBytes then
    IO.println s!"embedded bytes matched: {found.size} bytes"
    return 0
  IO.eprintln s!"embedded bytes differ: {file}"
  return 1
`);
  sources.set(`${prefix}.CheckDeclarations`, `import ${prefix}.ArtifactResult
import Project.Artifact.Binary.Proof.Decode
import Project.Artifact.Binary.Proof.Validate

open Wasm.Binary

example : decode ${artifact}.artifactBytes = .ok ${artifact}.Cache.raw :=
  ${artifact}.decode_eq_cache

example : Translation.module ${artifact}.Cache.raw =
    ${prefix}.«module» := by
  exact ${artifact}.translation_cache_eq

example :
    ∃ raw validated,
      decode ${artifact}.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      ${job.formalSpecDefinition} validated.toTalos :=
  ${artifact}.artifact_correct

#print axioms Wasm.Binary.Proof.decode_sound
#print axioms Wasm.Binary.Proof.validate_sound
#print axioms ${artifact}.decode_eq_cache
#print axioms ${artifact}.translation_cache_eq
#print axioms ${artifact}.artifact_module_eq_cache
#print axioms ${job.behaviorTheorem}
#print axioms ${artifact}.artifact_correct
`);
  return {
    sources,
    artifact: {
      sha256: digest,
      byteLength: wasmBytes.length,
      artifactBytesDefinition: `${artifact}.artifactBytes`,
      rawModuleDefinition: `${artifact}.Cache.raw`,
      programDefinition: `${prefix}.module`,
      property: job.formalSpecDefinition,
      behaviorTheorem: job.behaviorTheorem,
      artifactTheorem: `${artifact}.artifact_correct`,
      proofTarget: job.artifactTarget,
      checkFileTarget: `${prefix}.CheckFile`,
      declarationTarget: `${prefix}.CheckDeclarations`,
    },
  };
}

function jsonBytes(value) {
  return Buffer.from(`${JSON.stringify(value, null, 2)}\n`);
}

function writeAtomic(file, bytes) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  const temporary = `${file}.tmp-${process.pid}-${Date.now()}`;
  try {
    fs.writeFileSync(temporary, bytes, { flag: "wx" });
    fs.renameSync(temporary, file);
  } catch (error) {
    try {
      fs.rmSync(temporary, { force: true });
    } catch (cleanupError) {
      throw new AggregateError([error, cleanupError], `could not write ${file}`);
    }
    throw error;
  }
}

function collectFiles(root, relative = "") {
  const result = [];
  for (const entry of fs.readdirSync(path.join(root, relative), { withFileTypes: true })) {
    const child = path.join(relative, entry.name);
    if (entry.isSymbolicLink()) fail(`package contains symbolic link: ${child}`);
    if (entry.isDirectory()) result.push(...collectFiles(root, child));
    else if (entry.isFile()) result.push(child.split(path.sep).join("/"));
    else fail(`package contains unsupported file type: ${child}`);
  }
  return result.sort();
}

function fileRecords(root, excluded = new Set()) {
  return collectFiles(root).filter((file) => !excluded.has(file)).map((file) => {
    const bytes = fs.readFileSync(path.join(root, file));
    return { path: file, sha256: sha256(bytes), byteLength: bytes.length };
  });
}

function currentToolPins(repoRoot) {
  const conformance = JSON.parse(fs.readFileSync(
    path.join(repoRoot, "proofs", "talos", "conformance.json"), "utf8"));
  const lakeManifest = fs.readFileSync(
    path.join(repoRoot, "proofs", "talos", "lean", "lake-manifest.json"));
  const release = JSON.parse(fs.readFileSync(
    path.join(repoRoot, "proofs", "artifacts", "release.json"), "utf8"));
  const leanToolchain = fs.readFileSync(path.join(repoRoot, "lean-toolchain"), "utf8").trim();
  const proofKitHash = crypto.createHash("sha256");
  proofKitHash.update("leanexe-proof-kit-v1\0");
  for (const relative of proofKitRelativeFiles) {
    const absolute = path.join(repoRoot, ...relative.split("/"));
    const stat = fs.lstatSync(absolute);
    if (!stat.isFile() || stat.isSymbolicLink()) {
      fail(`invalid proof-kit file: ${relative}`);
    }
    const contents = fs.readFileSync(absolute);
    proofKitHash.update(`${relative}\0${contents.length}\0`);
    proofKitHash.update(contents);
  }
  if (!release.kernelReview || release.kernelReview.selectedToolchain !== leanToolchain ||
      !/^[0-9a-f]{40}$/.test(release.kernelReview.candidateCommit) ||
      !/^[0-9a-f]{64}$/.test(release.kernelReview.reproductionSha256) ||
      !["reproduction-rejected", "affected-accepted-after-source-audit"].includes(
        release.kernelReview.selectedResult) ||
      !release.kernelReview.scopeAudit ||
      JSON.stringify(release.kernelReview.scopeAudit.forbiddenIdentifiers) !==
        JSON.stringify(["addDecl", "inductDecl"])) {
    fail("release record does not contain an accepted kernel review");
  }
  return {
    leanToolchain,
    leanCommit: release.kernelReview.candidateCommit,
    talosRevision: expectedTalosRevision(repoRoot),
    proofLakeManifestSha256: sha256(lakeManifest),
    proofKitSourceSha256: proofKitHash.digest("hex"),
    verifierSourceSha256: verifierSourceSha256(repoRoot),
    nodeVersion: fs.readFileSync(path.join(repoRoot, ".node-version"), "utf8").trim(),
    wasmToolsVersion: fs.readFileSync(
      path.join(repoRoot, ".wasm-tools-version"), "utf8").trim(),
    wasmtimeVersion: conformance.wasmtimeVersion,
    kernelReview: {
      selectedResult: release.kernelReview.selectedResult,
      candidateCommit: release.kernelReview.candidateCommit,
      reproductionSha256: release.kernelReview.reproductionSha256,
      forbiddenIdentifiers: release.kernelReview.scopeAudit.forbiddenIdentifiers,
    },
  };
}

function kernelAuditFindings(sources, kernelReview) {
  if (kernelReview === null || typeof kernelReview !== "object" ||
      !Array.isArray(kernelReview.forbiddenIdentifiers)) {
    fail("kernel review does not contain forbidden identifiers");
  }
  const findings = [];
  for (const [moduleName, source] of [...sources].sort((left, right) =>
    left[0] < right[0] ? -1 : left[0] > right[0] ? 1 : 0)) {
    for (const [index, line] of source.split("\n").entries()) {
      for (const identifier of kernelReview.forbiddenIdentifiers) {
        if (new RegExp(`\\b${identifier}\\b`).test(line)) {
          findings.push(`${moduleName}:${index + 1}: ${identifier}`);
        }
      }
    }
  }
  return findings;
}

function installSources(root, sources) {
  for (const [moduleName, source] of sources) {
    writeAtomic(path.join(root, moduleFile(moduleName)), Buffer.from(source));
  }
}

function validateStageReports(stageReports, packageRoot, job) {
  exactKeys(stageReports,
    ["schemaVersion", "codexVersion", "maximumAttempts", "tasks"],
    "stage-reports.json");
  if (stageReports.schemaVersion !== 1) fail("unsupported stage report schema");
  requireString(stageReports.codexVersion, "stage-reports.json.codexVersion");
  if (!Number.isSafeInteger(stageReports.maximumAttempts) ||
      stageReports.maximumAttempts < 1 || stageReports.maximumAttempts > 10) {
    fail("stage-reports.json.maximumAttempts must be between 1 and 10");
  }
  exactKeys(stageReports.tasks,
    ["formalSpecification", "leanProgram", "artifactProof"],
    "stage-reports.json.tasks");
  const expected = {
    formalSpecification: ["formal-specification", job.formalSpecModule],
    leanProgram: ["lean-program", job.sourceModule],
    artifactProof: ["artifact-proof", job.behaviorModule],
  };
  for (const [key, [task, sourceModule]] of Object.entries(expected)) {
    const stage = stageReports.tasks[key];
    exactKeys(stage,
      ["task", "sourceModule", "sourceSha256", "reportSha256", "report"],
      `stage-reports.json.tasks.${key}`);
    if (stage.task !== task || stage.sourceModule !== sourceModule) {
      fail(`stage-reports.json.tasks.${key} has the wrong task identity`);
    }
    if (!/^[0-9a-f]{64}$/.test(stage.sourceSha256) ||
        !/^[0-9a-f]{64}$/.test(stage.reportSha256)) {
      fail(`stage-reports.json.tasks.${key} has an invalid SHA-256`);
    }
    exactKeys(stage.report, ["summary", "decisions", "attempts"],
      `stage-reports.json.tasks.${key}.report`);
    requireString(stage.report.summary,
      `stage-reports.json.tasks.${key}.report.summary`);
    requireStringArray(stage.report.decisions,
      `stage-reports.json.tasks.${key}.report.decisions`);
    if (!Array.isArray(stage.report.attempts) || stage.report.attempts.length === 0 ||
        stage.report.attempts.length > stageReports.maximumAttempts) {
      fail(`stage-reports.json.tasks.${key}.report.attempts has an invalid length`);
    }
    for (const [index, attempt] of stage.report.attempts.entries()) {
      exactKeys(attempt,
        ["number", "outcome", "sourceSha256", "diagnosticSha256", "diagnostic"],
        `stage-reports.json.tasks.${key}.report.attempts[${index}]`);
      if (attempt.number !== index + 1 || !["accepted", "rejected"].includes(attempt.outcome) ||
          !/^[0-9a-f]{64}$/.test(attempt.sourceSha256) ||
          !/^[0-9a-f]{64}$/.test(attempt.diagnosticSha256) ||
          typeof attempt.diagnostic !== "string" || attempt.diagnostic.length === 0 ||
          attempt.diagnosticSha256 !== sha256(Buffer.from(attempt.diagnostic))) {
        fail(`stage-reports.json.tasks.${key}.report.attempts[${index}] is invalid`);
      }
      if (attempt.outcome === "accepted" && index !== stage.report.attempts.length - 1) {
        fail(`stage-reports.json.tasks.${key} accepted before its final attempt`);
      }
    }
    const last = stage.report.attempts[stage.report.attempts.length - 1];
    if (last.outcome !== "accepted" || last.sourceSha256 !== stage.sourceSha256) {
      fail(`stage-reports.json.tasks.${key} has no accepted final source`);
    }
    if (stage.reportSha256 !== sha256(jsonBytes(stage.report))) {
      fail(`stage-reports.json.tasks.${key} report digest mismatch`);
    }
    const source = fs.readFileSync(path.join(packageRoot, "proof", moduleFile(sourceModule)));
    if (stage.sourceSha256 !== sha256(source)) {
      fail(`stage-reports.json.tasks.${key} source digest mismatch`);
    }
  }
  return stageReports;
}

function createPackage(stageRoot, values) {
  fs.mkdirSync(stageRoot, { recursive: true });
  writeAtomic(path.join(stageRoot, "request.txt"), Buffer.from(values.request));
  writeAtomic(path.join(stageRoot, "interpretation.json"), jsonBytes(values.interpretation));
  writeAtomic(path.join(stageRoot, "artifact.json"), jsonBytes(values.artifact));
  writeAtomic(path.join(stageRoot, "samples.json"), jsonBytes(values.samples));
  writeAtomic(path.join(stageRoot, "host-assumptions.json"), jsonBytes({
    hostAssumptions: values.hostAssumptions,
  }));
  writeAtomic(path.join(stageRoot, "stage-reports.json"), jsonBytes(values.stageReports));
  if (values.proofTelemetry !== undefined) {
    validateStage5Telemetry(
      values.proofTelemetry,
      values.stageReports.tasks.artifactProof.sourceSha256,
    );
    writeAtomic(path.join(stageRoot, "proof-telemetry.json"),
      jsonBytes(values.proofTelemetry));
  }
  if (values.proofJournal !== undefined) {
    writeAtomic(path.join(stageRoot, "proof-journal.md"),
      Buffer.from(validateProofJournal(values.proofJournal)));
  }
  writeAtomic(path.join(stageRoot, "tool-pins.json"), jsonBytes(values.toolPins));
  writeAtomic(path.join(stageRoot, "proof-library.md"), Buffer.from(values.proofLibraryCatalog));
  writeAtomic(path.join(stageRoot, "proof-strategies.md"), Buffer.from(values.proofStrategies));
  writeAtomic(path.join(stageRoot, "proof-task-features.json"),
    jsonBytes(values.proofTaskFeatures));
  if ((values.compilerAnnotations === undefined) !== (values.proofRecipes === undefined)) {
    fail("compiler annotations and proof recipes must appear together");
  }
  const annotated = values.compilerAnnotations !== undefined;
  if (annotated) {
    writeAtomic(path.join(stageRoot, "program.annotations.json"),
      jsonBytes(values.compilerAnnotations));
    writeAtomic(path.join(stageRoot, "proof-recipes.json"),
      jsonBytes(values.proofRecipes));
  }
  writeAtomic(path.join(stageRoot, "program.wasm"), values.wasmBytes);
  installSources(path.join(stageRoot, "proof"), values.sources);
  const manifest = {
    schemaVersion: annotated ? packageSchemaVersion : 4,
    requestSha256: sha256(Buffer.from(values.request)),
    case: values.job.caseName,
    leanModule: values.job.leanModule,
    sourceModule: values.job.sourceModule,
    formalSpecModule: values.job.formalSpecModule,
    formalSpecification: values.formalSpecification,
    artifact: values.artifact,
    warnings: values.warnings,
    verificationCommand: "tools/leanexegen verify <proof-package>",
    files: fileRecords(stageRoot),
  };
  writeAtomic(path.join(stageRoot, "package.json"), jsonBytes(manifest));
  return manifest;
}

function safePackagePath(root, relative) {
  if (typeof relative !== "string" || relative.length === 0 ||
      path.isAbsolute(relative) || relative.includes("\\")) {
    fail(`invalid package path: ${JSON.stringify(relative)}`);
  }
  const normalized = path.posix.normalize(relative);
  if (normalized !== relative || normalized.startsWith("../") || normalized === "..") {
    fail(`invalid package path: ${relative}`);
  }
  return path.join(root, ...relative.split("/"));
}

function validatePackage(packageRoot) {
  const manifestPath = path.join(packageRoot, "package.json");
  const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8"));
  exactKeys(manifest, [
    "schemaVersion",
    "requestSha256",
    "case",
    "leanModule",
    "sourceModule",
    "formalSpecModule",
    "formalSpecification",
    "artifact",
    "warnings",
    "verificationCommand",
    "files",
  ], "package.json");
  if (!supportedPackageSchemaVersions.has(manifest.schemaVersion)) {
    fail("unsupported package schema");
  }
  if (!/^[0-9a-f]{64}$/.test(manifest.requestSha256)) fail("invalid request SHA-256");
  if (!caseNamePattern.test(manifest.case) || snakeToPascal(manifest.case) !== manifest.leanModule) {
    fail("invalid package case identity");
  }
  const job = makeJob(fs.readFileSync(path.join(packageRoot, "request.txt"), "utf8"));
  for (const key of ["caseName", "leanModule", "sourceModule", "formalSpecModule"]) {
    const manifestKey = key === "caseName" ? "case" : key;
    if (manifest[manifestKey] !== job[key]) fail(`${manifestKey} disagrees with request.txt`);
  }
  if (manifest.requestSha256 !== job.requestSha256) fail("request digest mismatch");
  exactKeys(manifest.formalSpecification,
    ["module", "definition", "type"], "formalSpecification");
  if (manifest.formalSpecification.module !== job.formalSpecModule) {
    fail("formal specification module disagrees with request.txt");
  }
  if (manifest.formalSpecification.definition !== job.formalSpecDefinition ||
      manifest.formalSpecification.type !== job.formalSpecType) {
    fail("formal specification declaration disagrees with the fixed interface");
  }
  requireStringArray(manifest.warnings, "warnings", false);
  if (manifest.verificationCommand !== "tools/leanexegen verify <proof-package>") {
    fail("unsupported verification command");
  }
  exactKeys(manifest.artifact, [
    "sha256",
    "byteLength",
    "artifactBytesDefinition",
    "rawModuleDefinition",
    "programDefinition",
    "property",
    "behaviorTheorem",
    "artifactTheorem",
    "proofTarget",
    "checkFileTarget",
    "declarationTarget",
    "export",
    "invocation",
  ], "artifact");
  if (!/^[0-9a-f]{64}$/.test(manifest.artifact.sha256) ||
      !Number.isSafeInteger(manifest.artifact.byteLength) ||
      manifest.artifact.byteLength < 0) {
    fail("invalid artifact byte identity");
  }
  const artifactPrefix = `${job.namespace}.Artifact`;
  const exactArtifactNames = {
    artifactBytesDefinition: `${artifactPrefix}.artifactBytes`,
    rawModuleDefinition: `${artifactPrefix}.Cache.raw`,
    programDefinition: `${job.namespace}.module`,
    artifactTheorem: `${artifactPrefix}.artifact_correct`,
    proofTarget: job.artifactTarget,
    checkFileTarget: `${job.namespace}.CheckFile`,
    declarationTarget: `${job.namespace}.CheckDeclarations`,
  };
  for (const [key, expected] of Object.entries(exactArtifactNames)) {
    if (manifest.artifact[key] !== expected) fail(`artifact.${key} must be ${expected}`);
  }
  if (manifest.artifact.property !== job.formalSpecDefinition ||
      manifest.artifact.behaviorTheorem !== job.behaviorTheorem) {
    fail("artifact theorem names disagree with the fixed interface");
  }
  requireString(manifest.artifact.export, "artifact.export");
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(manifest.artifact.export)) {
    fail("artifact.export must be a WebAssembly identifier");
  }
  if (!Array.isArray(manifest.artifact.invocation) ||
      manifest.artifact.invocation.length < 3 ||
      manifest.artifact.invocation.some((item) => typeof item !== "string")) {
    fail("artifact.invocation must be a command argument array");
  }
  if (!Array.isArray(manifest.files) || manifest.files.length === 0) {
    fail("package files must be a nonempty array");
  }
  const seen = new Set();
  for (const [index, record] of manifest.files.entries()) {
    exactKeys(record, ["path", "sha256", "byteLength"], `files[${index}]`);
    const file = safePackagePath(packageRoot, record.path);
    if (record.path === "package.json" || seen.has(record.path)) {
      fail(`invalid or duplicate package file: ${record.path}`);
    }
    seen.add(record.path);
    const stat = fs.lstatSync(file);
    if (!stat.isFile() || stat.isSymbolicLink()) fail(`invalid package file: ${record.path}`);
    const bytes = fs.readFileSync(file);
    if (!/^[0-9a-f]{64}$/.test(record.sha256) || record.sha256 !== sha256(bytes) ||
        !Number.isSafeInteger(record.byteLength) || record.byteLength !== bytes.length) {
      fail(`package file identity mismatch: ${record.path}`);
    }
  }
  const actual = collectFiles(packageRoot).filter((file) => file !== "package.json");
  if (actual.length !== seen.size || actual.some((file) => !seen.has(file))) {
    fail("package file set differs from package.json");
  }
  const artifact = JSON.parse(fs.readFileSync(path.join(packageRoot, "artifact.json"), "utf8"));
  if (JSON.stringify(artifact) !== JSON.stringify(manifest.artifact)) {
    fail("artifact.json differs from package.json");
  }
  const wasm = fs.readFileSync(path.join(packageRoot, "program.wasm"));
  if (artifact.sha256 !== sha256(wasm) || artifact.byteLength !== wasm.length) {
    fail("program.wasm differs from artifact identity");
  }
  const assumptions = JSON.parse(fs.readFileSync(
    path.join(packageRoot, "host-assumptions.json"), "utf8"));
  exactKeys(assumptions, ["hostAssumptions"], "host-assumptions.json");
  requireStringArray(assumptions.hostAssumptions,
    "host-assumptions.json.hostAssumptions");
  validateProgramImports(job, fs.readFileSync(
    path.join(packageRoot, "proof", moduleFile(job.sourceModule)), "utf8"));
  const stageReports = validateStageReports(JSON.parse(fs.readFileSync(
    path.join(packageRoot, "stage-reports.json"), "utf8")), packageRoot, job);
  const proofTelemetry = seen.has("proof-telemetry.json")
    ? validateStage5Telemetry(JSON.parse(fs.readFileSync(
      path.join(packageRoot, "proof-telemetry.json"), "utf8")),
    stageReports.tasks.artifactProof.sourceSha256)
    : null;
  const proofJournal = seen.has("proof-journal.md")
    ? validateProofJournal(fs.readFileSync(
      path.join(packageRoot, "proof-journal.md"), "utf8"), "proof-journal.md")
    : null;
  const requiredFiles = [
    "request.txt",
    "interpretation.json",
    "artifact.json",
    "samples.json",
    "host-assumptions.json",
    "stage-reports.json",
    "tool-pins.json",
    "proof-library.md",
    "program.wasm",
    `proof/${moduleFile(job.sourceModule)}`,
    `proof/${moduleFile(job.formalSpecModule)}`,
    `proof/${moduleFile(job.programModule)}`,
    `proof/${moduleFile(job.artifactTarget)}`,
    `proof/${moduleFile(manifest.artifact.checkFileTarget)}`,
    `proof/${moduleFile(manifest.artifact.declarationTarget)}`,
  ];
  if (manifest.schemaVersion >= 4) {
    requiredFiles.push("proof-strategies.md", "proof-task-features.json");
    const strategyNotes = fs.readFileSync(
      path.join(packageRoot, "proof-strategies.md"), "utf8");
    if (!strategyNotes.startsWith("# Selected Talos Artifact-Proof Strategies\n\n")) {
      fail("proof-strategies.md has an invalid heading");
    }
    const features = JSON.parse(fs.readFileSync(
      path.join(packageRoot, "proof-task-features.json"), "utf8"));
    exactKeys(features, [
      "schemaVersion",
      "extractorVersion",
      "sourceSha256",
      "exportIndex",
      "reachableFunctions",
      "selectedSections",
    ], "proof-task-features.json");
    if (features.schemaVersion !== 1 ||
        ![1, 2, 3, 4, 5].includes(features.extractorVersion) ||
        !/^[0-9a-f]{64}$/.test(features.sourceSha256) ||
        features.exportIndex !== programExportIndex(fs.readFileSync(
          path.join(packageRoot, "proof", moduleFile(job.programModule)), "utf8"),
        job.exportName)) {
      fail("proof-task-features.json has an invalid identity");
    }
    if (!Array.isArray(features.reachableFunctions) ||
        features.reachableFunctions.length === 0 ||
        !features.reachableFunctions.some((item) => item?.index === features.exportIndex)) {
      fail("proof-task-features.json has invalid reachable functions");
    }
    if (features.extractorVersion >= 2) {
      for (const [functionIndex, function_] of features.reachableFunctions.entries()) {
        const functionKeys = [
          "index", "instructionCount", "localCount", "calls", "loopCount",
          "hasMemory", "hasArithmetic", "hasAllocation", "fixedArrayEqNodes",
        ];
        if (features.extractorVersion >= 4) functionKeys.push("fixedArraySearchKeys");
        if (features.extractorVersion >= 5) functionKeys.push("fixedArrayLengthDispatches");
        exactKeys(function_, functionKeys,
          `proof-task-features.json.reachableFunctions[${functionIndex}]`);
        if (!Array.isArray(function_.fixedArrayEqNodes)) {
          fail(`proof-task-features.json function ${functionIndex} has invalid equality nodes`);
        }
        for (const [nodeIndex, node] of function_.fixedArrayEqNodes.entries()) {
          exactKeys(node, features.extractorVersion === 2 ?
            ["offset", "index", "keyLocal"] :
            ["offset", "index", "keyLocal", "order"],
            `proof-task-features.json equality node ${functionIndex}:${nodeIndex}`);
          if (![node.offset, node.index, node.keyLocal].every(
            (value) => Number.isSafeInteger(value) && value >= 0) ||
              (features.extractorVersion === 3 &&
                !["loaded-first", "key-first"].includes(node.order))) {
            fail(`proof-task-features.json equality node ${functionIndex}:${nodeIndex} is invalid`);
          }
        }
        if (features.extractorVersion >= 4) {
          if (!Array.isArray(function_.fixedArraySearchKeys)) {
            fail(`proof-task-features.json function ${functionIndex} has invalid search keys`);
          }
          for (const [keyIndex, key] of function_.fixedArraySearchKeys.entries()) {
            exactKeys(key, ["offset", "index", "keyLocal"],
              `proof-task-features.json search key ${functionIndex}:${keyIndex}`);
            if (![key.offset, key.index, key.keyLocal].every(
              (value) => Number.isSafeInteger(value) && value >= 0)) {
              fail(`proof-task-features.json search key ${functionIndex}:${keyIndex} is invalid`);
            }
          }
        }
        if (features.extractorVersion >= 5) {
          if (!Array.isArray(function_.fixedArrayLengthDispatches)) {
            fail(`proof-task-features.json function ${functionIndex} has invalid length dispatches`);
          }
          for (const [dispatchIndex, dispatch] of
            function_.fixedArrayLengthDispatches.entries()) {
            exactKeys(dispatch, ["inputLocal", "expectedSize"],
              `proof-task-features.json length dispatch ${functionIndex}:${dispatchIndex}`);
            if (![dispatch.inputLocal, dispatch.expectedSize].every(
              (value) => Number.isSafeInteger(value) && value >= 0)) {
              fail(`proof-task-features.json length dispatch ${functionIndex}:${dispatchIndex} is invalid`);
            }
          }
        }
      }
    }
    if (!Array.isArray(features.selectedSections) || features.selectedSections.length === 0) {
      fail("proof-task-features.json has no selected sections");
    }
    const selected = new Set();
    for (const [index, item] of features.selectedSections.entries()) {
      exactKeys(item, ["id", "reason"], `proof-task-features.json.selectedSections[${index}]`);
      if (typeof item.id !== "string" || !/^strategy\.[a-z]+$/.test(item.id) ||
          selected.has(item.id) || typeof item.reason !== "string" || item.reason.length === 0 ||
          !strategyNotes.includes(`### \`${item.id}\``)) {
        fail(`proof-task-features.json has invalid selected section ${index}`);
      }
      selected.add(item.id);
    }
  }
  let compilerAnnotations = null;
  let proofRecipes = null;
  if (manifest.schemaVersion >= 5) {
    requiredFiles.push("program.annotations.json", "proof-recipes.json");
    compilerAnnotations = validateAnnotationDocument(JSON.parse(fs.readFileSync(
      path.join(packageRoot, "program.annotations.json"), "utf8")), wasm);
    const programSource = fs.readFileSync(
      path.join(packageRoot, "proof", moduleFile(job.programModule)), "utf8");
    matchAnnotationDocument(compilerAnnotations, programSource);
    proofRecipes = validateProofRecipePlan(JSON.parse(fs.readFileSync(
      path.join(packageRoot, "proof-recipes.json"), "utf8")), compilerAnnotations);
  }
  for (const required of requiredFiles) {
    if (!seen.has(required)) fail(`package is missing ${required}`);
  }
  const proofRoot = path.join(packageRoot, "proof");
  for (const relative of collectFiles(proofRoot)) {
    if (!relative.endsWith(".lean")) fail(`unexpected proof package file: ${relative}`);
    const moduleName = relative.slice(0, -5).split("/").join(".");
    if (moduleName === job.sourceModule) continue;
    const source = fs.readFileSync(path.join(proofRoot, ...relative.split("/")), "utf8");
    for (const imported of imports(source)) {
      const allowedDependency = imported === "CodeLib" ||
        imported.startsWith("CodeLib.") ||
        imported.startsWith("Init.") ||
        imported.startsWith("Std.") ||
        imported.startsWith("Mathlib.") ||
        imported.startsWith("Interpreter.") ||
        imported.startsWith("Project.Artifact.Binary.");
      const allowedProofKit = proofKitModules.includes(imported);
      const allowedGenerated = imported.startsWith(`${job.namespace}.`) &&
        imported !== job.sourceModule;
      if (!allowedDependency && !allowedProofKit && !allowedGenerated) {
        fail(`${moduleName} imports unsupported proof dependency ${imported}`);
      }
    }
  }
  return {
    manifest,
    job,
    artifact,
    wasm,
    stageReports,
    proofTelemetry,
    proofJournal,
    compilerAnnotations,
    proofRecipes,
  };
}

module.exports = {
  artifactSources,
  codexTaskSchemaVersion,
  collectFiles,
  createPackage,
  currentToolPins,
  exactKeys,
  installSources,
  imports,
  kernelAuditFindings,
  makeJob,
  moduleFile,
  packageSchemaVersion,
  programExportIndex,
  proofKitModules,
  rewriteProgramNamespace,
  sha256,
  validateCodexTaskOutcome,
  validatePackage,
  validateProofJournal,
  validateProgramImports,
  validateProofImports,
  validateStageReports,
  writeAtomic,
};
