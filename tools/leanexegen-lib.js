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
const packageSchemaVersion = 9;
const supportedPackageSchemaVersions = new Set([3, 4, 5, 6, 7, 8, packageSchemaVersion]);
const caseNamePattern = /^[a-z][a-z0-9]*(?:_[a-z0-9]+)*$/;
const ltgIdPattern = /^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/;
const knowledgeModulePattern = /^LeanExeGen\.Knowledge\.[A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)+$/;
const decimalPattern = /^(?:0|[1-9][0-9]*)$/;
const uint64Maximum = 18446744073709551615n;
const proofKitModules = Object.freeze([
  "Project.ProofKit.Annotation",
  "Project.ProofKit.Memory",
  "Project.ProofKit.Frame",
  "Project.ProofKit.Array",
  "Project.ProofKit.Allocation",
  "Project.ProofKit.FixedArrayCapacity",
  "Project.ProofKit.FixedArrayCopy",
  "Project.ProofKit.FixedArrayAllocator",
  "Project.ProofKit.FixedArrayAllocatorWindow",
  "Project.ProofKit.FixedArrayEqNode",
  "Project.ProofKit.FixedArrayFilterLt",
  "Project.ProofKit.FixedArrayFindIdxEq",
  "Project.ProofKit.FixedArrayFold",
  "Project.ProofKit.FixedArrayFoldBody",
  "Project.ProofKit.FixedArrayInput",
  "Project.ProofKit.FixedArrayLengthDispatch",
  "Project.ProofKit.FixedArrayLtNode",
  "Project.ProofKit.FixedArrayMapAdd",
  "Project.ProofKit.FixedArrayPairResult",
  "Project.ProofKit.FixedArrayResult",
  "Project.ProofKit.FixedArraySearch",
  "Project.ProofKit.FixedArraySearchChain",
  "Project.ProofKit.FixedArraySearchTree",
  "Project.ProofKit.FixedArraySingleton",
  "Project.ProofKit.FixedArraySingletonWrapper",
  "Project.ProofKit.FixedArrayTraversalInput",
  "Project.ProofKit.Control",
  "Project.ProofKit.GuardedBackEdge",
  "Project.ProofKit.ScalarTransition",
  "Project.ProofKit.ScalarTransitionU64",
]);
const proofKitRelativeFiles = Object.freeze([
  "proofs/talos/lean/Project/ProofKit/Annotation.lean",
  "proofs/talos/lean/Project/ProofKit/Memory.lean",
  "proofs/talos/lean/Project/ProofKit/Frame.lean",
  "proofs/talos/lean/Project/ProofKit/Array.lean",
  "proofs/talos/lean/Project/ProofKit/Allocation.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayCapacity.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayCopy.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayAllocator.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayAllocatorWindow.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayEqNode.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayFilterLt.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayFindIdxEq.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayFold.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayFoldBody.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayInput.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayLengthDispatch.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayLtNode.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayMapAdd.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayPairResult.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayResult.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySearch.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySearchChain.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySearchTree.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySingleton.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArraySingletonWrapper.lean",
  "proofs/talos/lean/Project/ProofKit/FixedArrayTraversalInput.lean",
  "proofs/talos/lean/Project/ProofKit/Control.lean",
  "proofs/talos/lean/Project/ProofKit/GuardedBackEdge.lean",
  "proofs/talos/lean/Project/ProofKit/ScalarTransition.lean",
  "proofs/talos/lean/Project/ProofKit/ScalarTransitionU64.lean",
  "proofs/talos/lean/Project/ProofKit/README.md",
]);

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function ltgFilesDigest(files) {
  const hash = crypto.createHash("sha256");
  hash.update("leanexe-ltg-task-v1\0");
  for (const [relative, source] of [...files].sort(([left], [right]) =>
    left.localeCompare(right))) {
    hash.update(relative);
    hash.update("\0");
    hash.update(source);
    hash.update("\0");
  }
  return hash.digest("hex");
}

function knowledgeFilesDigest(files) {
  const hash = crypto.createHash("sha256");
  hash.update("leanexe-knowledge-task-v1\0");
  for (const [relative, source] of [...files].sort(([left], [right]) =>
    left.localeCompare(right))) {
    hash.update(relative);
    hash.update("\0");
    hash.update(source);
    hash.update("\0");
  }
  return hash.digest("hex");
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

function knowledgePackagePascal(name) {
  return name.split("-").map((part) =>
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
    heapReserveDefinition: `${prefix}.FormalSpec.heapReserveBytes`,
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

function validateProofImports(job, modules, additionalModules = new Set()) {
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
      const allowedProofKit = proofKitModules.includes(imported) || additionalModules.has(imported);
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

function stageReportCodexVersions(stageReports) {
  if (stageReports.schemaVersion === 1) {
    return {
      formalSpecification: stageReports.codexVersion,
      leanProgram: stageReports.codexVersion,
      artifactProof: stageReports.codexVersion,
    };
  }
  return structuredClone(stageReports.codexVersions);
}

function stageReportCodexVersion(stageReports, task) {
  return stageReportCodexVersions(stageReports)[task];
}

function validateStageReports(stageReports, packageRoot, job) {
  if (stageReports.schemaVersion === 1) {
    exactKeys(stageReports,
      ["schemaVersion", "codexVersion", "maximumAttempts", "tasks"],
      "stage-reports.json");
    requireString(stageReports.codexVersion, "stage-reports.json.codexVersion");
  } else if (stageReports.schemaVersion === 2) {
    exactKeys(stageReports,
      ["schemaVersion", "codexVersions", "maximumAttempts", "tasks"],
      "stage-reports.json");
    exactKeys(stageReports.codexVersions,
      ["artifactProof", "formalSpecification", "leanProgram"],
      "stage-reports.json.codexVersions");
    for (const task of ["formalSpecification", "leanProgram", "artifactProof"]) {
      requireString(stageReports.codexVersions[task],
        `stage-reports.json.codexVersions.${task}`);
    }
  } else {
    fail("unsupported stage report schema");
  }
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

function validateLtgTask(document, files, artifactSha256) {
  exactKeys(document, [
    "schemaVersion", "artifactSha256", "derivativeGroups", "entries", "entryIds",
    "excludedEntries", "excludedEntryIds", "sha256",
  ], "ltg-task.json");
  if (document.schemaVersion !== 1 || document.artifactSha256 !== artifactSha256) {
    fail("ltg-task.json has an invalid schema or artifact identity");
  }
  const derivativeGroups = requireStringArray(
    document.derivativeGroups, "ltg-task.json.derivativeGroups");
  const entryIds = requireStringArray(document.entryIds, "ltg-task.json.entryIds");
  const excludedEntryIds = requireStringArray(
    document.excludedEntryIds, "ltg-task.json.excludedEntryIds");
  for (const [description, values] of [
    ["derivativeGroups", derivativeGroups],
    ["entryIds", entryIds],
    ["excludedEntryIds", excludedEntryIds],
  ]) {
    if (values.some((value, index) => index > 0 && values[index - 1] > value)) {
      fail(`ltg-task.json.${description} must be sorted`);
    }
  }
  if (derivativeGroups.some((value) => !ltgIdPattern.test(value)) ||
      entryIds.some((value) => !ltgIdPattern.test(value)) ||
      excludedEntryIds.some((value) => !ltgIdPattern.test(value))) {
    fail("ltg-task.json contains an invalid identifier");
  }
  const excludedEntryIdSet = new Set(excludedEntryIds);
  if (entryIds.some((entryId) => excludedEntryIdSet.has(entryId)) ||
      document.entries !== entryIds.length ||
      document.excludedEntries !== excludedEntryIds.length) {
    fail("ltg-task.json has inconsistent entry counts or exclusions");
  }
  const includedEntryIds = new Set(entryIds);
  if (!(files instanceof Map) || files.size === 0 ||
      !files.has("README.md") || !files.has("categories.json")) {
    fail("archived LTG must contain README.md and categories.json");
  }
  for (const relative of files.keys()) {
    if (typeof relative !== "string" || relative.length === 0 ||
        path.isAbsolute(relative) || relative.includes("\\") ||
        path.posix.normalize(relative) !== relative || relative.startsWith("../")) {
      fail(`archived LTG has an invalid path: ${JSON.stringify(relative)}`);
    }
  }
  if (!/^[0-9a-f]{64}$/.test(document.sha256) ||
      document.sha256 !== ltgFilesDigest(files)) {
    fail("ltg-task.json digest differs from the archived LTG");
  }
  let categories;
  try {
    categories = JSON.parse(files.get("categories.json").toString("utf8"));
  } catch (error) {
    fail(`archived LTG categories.json is invalid: ${error.message}`);
  }
  exactKeys(categories, ["schemaVersion", "categories"], "archived LTG categories.json");
  if (categories.schemaVersion !== 1 || !Array.isArray(categories.categories) ||
      categories.categories.length === 0) {
    fail("archived LTG categories.json has an unsupported schema or no categories");
  }
  const categoryIds = [];
  for (const [index, category] of categories.categories.entries()) {
    exactKeys(category, ["id", "title", "summary"], `archived LTG category ${index}`);
    if (!ltgIdPattern.test(category.id)) fail(`archived LTG category ${index} has an invalid id`);
    requireString(category.title, `archived LTG category ${index} title`);
    requireString(category.summary, `archived LTG category ${index} summary`);
    categoryIds.push(category.id);
  }
  if (new Set(categoryIds).size !== categoryIds.length ||
      categoryIds.some((value, index) => index > 0 && categoryIds[index - 1] > value)) {
    fail("archived LTG categories must have unique sorted identifiers");
  }
  const categoryIdSet = new Set(categoryIds);
  for (const relative of files.keys()) {
    if (relative === "README.md" || relative === "categories.json") continue;
    const categoryMatch = relative.match(/^categories\/([^/]+)\/tools\.jsonl$/);
    if (categoryMatch !== null && categoryIdSet.has(categoryMatch[1])) continue;
    const entryMatch = relative.match(/^entries\/([^/]+)\/.+$/);
    if (entryMatch !== null && includedEntryIds.has(entryMatch[1])) continue;
    fail(`archived LTG contains an unindexed path: ${relative}`);
  }
  const indexedEntries = new Set();
  for (const [index, category] of categories.categories.entries()) {
    const indexPath = `categories/${category.id}/tools.jsonl`;
    if (!files.has(indexPath)) fail(`archived LTG is missing ${indexPath}`);
    const lines = files.get(indexPath).toString("utf8").split("\n").filter(Boolean);
    const categoryEntries = new Set();
    for (const [lineIndex, line] of lines.entries()) {
      let record;
      try {
        record = JSON.parse(line);
      } catch (error) {
        fail(`${indexPath}:${lineIndex + 1} is invalid JSON: ${error.message}`);
      }
      if (record === null || typeof record !== "object" ||
          !includedEntryIds.has(record.id) ||
          record.path !== `../../entries/${record.id}` ||
          categoryEntries.has(record.id)) {
        fail(`${indexPath}:${lineIndex + 1} has an invalid entry reference`);
      }
      categoryEntries.add(record.id);
      indexedEntries.add(record.id);
    }
  }
  for (const entryId of entryIds) {
    if (!indexedEntries.has(entryId) ||
        !files.has(`entries/${entryId}/entry.json`) ||
        !files.has(`entries/${entryId}/README.md`)) {
      fail(`archived LTG entry ${entryId} is incomplete or unindexed`);
    }
  }
  const archivedPaths = [...files.keys()];
  for (const entryId of excludedEntryIds) {
    if (archivedPaths.some((relative) => relative.startsWith(`entries/${entryId}/`))) {
      fail(`archived LTG contains excluded entry ${entryId}`);
    }
  }
  return { manifest: structuredClone(document), files: new Map(files) };
}

function validateKnowledgeTask(document, files, artifactSha256) {
  if (document === null || typeof document !== "object" ||
      ![1, 2].includes(document.schemaVersion)) {
    fail("knowledge-task.json has an unsupported schema");
  }
  exactKeys(document, document.schemaVersion === 1 ? [
    "schemaVersion", "artifactSha256", "derivativeGroups", "packages", "entries",
    "excludedEntries", "sha256",
  ] : [
    "schemaVersion", "artifactSha256", "packages", "entries", "excludedEntries", "sha256",
  ], "knowledge-task.json");
  if (document.artifactSha256 !== artifactSha256) {
    fail("knowledge-task.json has an invalid schema or artifact identity");
  }
  if (document.schemaVersion === 1) {
    const derivativeGroups = requireStringArray(
      document.derivativeGroups, "knowledge-task.json.derivativeGroups");
    if (derivativeGroups.some((value) => !ltgIdPattern.test(value)) ||
        derivativeGroups.some((value, index) =>
          index > 0 && derivativeGroups[index - 1] > value)) {
      fail("knowledge-task.json.derivativeGroups must contain sorted identifiers");
    }
  }
  if (!(files instanceof Map) || !files.has("forest.json")) {
    fail("archived knowledge must contain forest.json");
  }
  for (const relative of files.keys()) {
    if (typeof relative !== "string" || relative.length === 0 || path.isAbsolute(relative) ||
        relative.includes("\\") || path.posix.normalize(relative) !== relative ||
        relative.startsWith("../")) {
      fail(`archived knowledge has an invalid path: ${JSON.stringify(relative)}`);
    }
  }
  if (!/^[0-9a-f]{64}$/.test(document.sha256) ||
      document.sha256 !== knowledgeFilesDigest(files)) {
    fail("knowledge-task.json digest differs from the archived knowledge");
  }
  if (!Array.isArray(document.packages) || document.packages.length === 0) {
    fail("knowledge-task.json.packages must be a nonempty array");
  }
  let taskForest;
  try {
    taskForest = JSON.parse(files.get("forest.json").toString("utf8"));
  } catch (error) {
    fail(`archived knowledge forest is invalid: ${error.message}`);
  }
  exactKeys(taskForest, ["schemaVersion", "packages"], "archived knowledge forest");
  if (taskForest.schemaVersion !== 1 || !Array.isArray(taskForest.packages)) {
    fail("archived knowledge forest has an unsupported schema");
  }
  const packageIds = new Set();
  const entryIds = new Set();
  const leanSources = new Map();
  const packageSources = new Map();
  let entries = 0;
  let excludedEntries = 0;
  for (const [index, record] of document.packages.entries()) {
    exactKeys(record, [
      "id", "version", "maturity", "dependencies", "entries", "entryIds",
      "excludedEntries", "excludedEntryIds", "leanModules", "sha256",
    ], `knowledge-task.json.packages[${index}]`);
    const packageId = requireString(record.id, `knowledge package ${index} id`);
    if (!ltgIdPattern.test(packageId) || packageIds.has(packageId) ||
        (index > 0 && document.packages[index - 1].id > packageId)) {
      fail("knowledge-task.json packages must have unique sorted identifiers");
    }
    packageIds.add(packageId);
    if (!Number.isSafeInteger(record.version) || record.version < 1 ||
        !["experimental", "promoted"].includes(record.maturity)) {
      fail(`knowledge package ${packageId} has an invalid version or maturity`);
    }
    const dependencies = requireStringArray(
      record.dependencies, `knowledge package ${packageId} dependencies`);
    const included = requireStringArray(record.entryIds,
      `knowledge package ${packageId} entryIds`);
    const excluded = requireStringArray(record.excludedEntryIds,
      `knowledge package ${packageId} excludedEntryIds`);
    const leanModules = requireStringArray(record.leanModules,
      `knowledge package ${packageId} leanModules`);
    for (const [description, values] of [
      ["dependencies", dependencies], ["entryIds", included],
      ["excludedEntryIds", excluded], ["leanModules", leanModules],
    ]) {
      if (values.some((value, itemIndex) => itemIndex > 0 && values[itemIndex - 1] > value)) {
        fail(`knowledge package ${packageId} ${description} must be sorted`);
      }
    }
    if (dependencies.some((dependency) =>
      !ltgIdPattern.test(dependency) || dependency === packageId) ||
        included.some((entryId) => !ltgIdPattern.test(entryId)) ||
        excluded.some((entryId) => !ltgIdPattern.test(entryId)) ||
        leanModules.some((moduleName) => !knowledgeModulePattern.test(moduleName))) {
      fail(`knowledge package ${packageId} contains an invalid identifier`);
    }
    if (!Number.isSafeInteger(record.entries) || record.entries !== included.length ||
        !Number.isSafeInteger(record.excludedEntries) ||
        record.excludedEntries !== excluded.length ||
        included.some((entryId) => excluded.includes(entryId))) {
      fail(`knowledge package ${packageId} has inconsistent entry counts`);
    }
    for (const entryId of included) {
      if (entryIds.has(entryId)) fail(`duplicate archived knowledge entry ${entryId}`);
      entryIds.add(entryId);
    }
    entries += included.length;
    excludedEntries += excluded.length;
    const prefix = `packages/${packageId}/`;
    const packageFiles = new Map([...files]
      .filter(([relative]) => relative.startsWith(prefix))
      .map(([relative, source]) => [relative.slice(prefix.length), source]));
    if (!packageFiles.has("knowledge-package.json") ||
        !packageFiles.has("catalog/README.md") ||
        !packageFiles.has("catalog/categories.json") ||
        !/^[0-9a-f]{64}$/.test(record.sha256) ||
        record.sha256 !== knowledgeFilesDigest(packageFiles)) {
      fail(`knowledge package ${packageId} has an incomplete archive or wrong digest`);
    }
    let packageManifest;
    try {
      packageManifest = JSON.parse(packageFiles.get("knowledge-package.json").toString("utf8"));
    } catch (error) {
      fail(`knowledge package ${packageId} manifest is invalid: ${error.message}`);
    }
    exactKeys(packageManifest, [
      "schemaVersion", "id", "version", "title", "summary", "maturity",
      "dependencies", "catalogRoot", "leanSources", "evidence",
    ], `knowledge package ${packageId} manifest`);
    if (packageManifest.schemaVersion !== 1 || packageManifest.id !== packageId ||
        packageManifest.version !== record.version ||
        packageManifest.maturity !== record.maturity ||
        JSON.stringify(packageManifest.dependencies) !== JSON.stringify(dependencies) ||
        packageManifest.catalogRoot !== "catalog" ||
        !Array.isArray(packageManifest.leanSources) ||
        !Array.isArray(packageManifest.evidence)) {
      fail(`knowledge package ${packageId} manifest disagrees with the task record`);
    }
    requireString(packageManifest.title, `knowledge package ${packageId} title`);
    requireString(packageManifest.summary, `knowledge package ${packageId} summary`);
    const declaredSources = new Map();
    const expectedModulePrefix =
      `LeanExeGen.Knowledge.${knowledgePackagePascal(packageId)}.`;
    for (const [sourceIndex, sourceRecord] of packageManifest.leanSources.entries()) {
      exactKeys(sourceRecord, ["module", "path"],
        `knowledge package ${packageId} source ${sourceIndex}`);
      requireString(sourceRecord.module,
        `knowledge package ${packageId} source ${sourceIndex} module`);
      requireString(sourceRecord.path,
        `knowledge package ${packageId} source ${sourceIndex} path`);
      if (!knowledgeModulePattern.test(sourceRecord.module) ||
          !sourceRecord.module.startsWith(expectedModulePrefix) ||
          sourceRecord.path !== `lean/${moduleFile(sourceRecord.module)}` ||
          declaredSources.has(sourceRecord.module)) {
        fail(`knowledge package ${packageId} has an invalid source record`);
      }
      declaredSources.set(sourceRecord.module, sourceRecord.path);
    }
    if (declaredSources.size !== leanModules.length ||
        [...declaredSources.keys()].some((moduleName, sourceIndex) =>
          moduleName !== leanModules[sourceIndex])) {
      fail(`knowledge package ${packageId} source manifest differs from its task record`);
    }
    const selectedPackageSources = new Map();
    for (const moduleName of leanModules) {
      const sourcePath = declaredSources.get(moduleName);
      if (sourcePath === undefined || !packageFiles.has(sourcePath) ||
          leanSources.has(moduleName)) {
        fail(`knowledge package ${packageId} is missing source module ${moduleName}`);
      }
      const source = packageFiles.get(sourcePath).toString("utf8");
      leanSources.set(moduleName, source);
      selectedPackageSources.set(moduleName, source);
    }
    packageSources.set(packageId, selectedPackageSources);
    const includedSourcePaths = new Set(leanModules.map((moduleName) =>
      declaredSources.get(moduleName)));
    const declaredEvidence = new Map();
    for (const [evidenceIndex, evidenceRecord] of packageManifest.evidence.entries()) {
      exactKeys(evidenceRecord, ["path", "entries"],
        `knowledge package ${packageId} evidence ${evidenceIndex}`);
      requireString(evidenceRecord.path,
        `knowledge package ${packageId} evidence ${evidenceIndex} path`);
      const boundEntries = requireStringArray(evidenceRecord.entries,
        `knowledge package ${packageId} evidence ${evidenceIndex} entries`, false);
      if (!evidenceRecord.path.startsWith("evidence/") ||
          path.posix.normalize(evidenceRecord.path) !== evidenceRecord.path ||
          declaredEvidence.has(evidenceRecord.path) ||
          boundEntries.some((entryId) => !included.includes(entryId)) ||
          !packageFiles.has(evidenceRecord.path)) {
        fail(`knowledge package ${packageId} has an invalid evidence record`);
      }
      declaredEvidence.set(evidenceRecord.path, boundEntries);
    }
    for (const relative of packageFiles.keys()) {
      if (relative === "knowledge-package.json" || relative === "catalog/README.md" ||
          relative === "catalog/categories.json" ||
          /^catalog\/categories\/[^/]+\/tools\.jsonl$/.test(relative) ||
          /^catalog\/entries\/[^/]+\/.+$/.test(relative)) {
        continue;
      }
      if (relative.startsWith("lean/") && includedSourcePaths.has(relative)) continue;
      if (relative.startsWith("evidence/") && declaredEvidence.has(relative) &&
          declaredEvidence.get(relative).some((entryId) => included.includes(entryId))) {
        continue;
      }
      fail(`knowledge package ${packageId} contains unselected path ${relative}`);
    }
    let categories;
    try {
      categories = JSON.parse(packageFiles.get("catalog/categories.json").toString("utf8"));
    } catch (error) {
      fail(`knowledge package ${packageId} categories are invalid: ${error.message}`);
    }
    exactKeys(categories, ["schemaVersion", "categories"],
      `knowledge package ${packageId} categories`);
    if (categories.schemaVersion !== 1 || !Array.isArray(categories.categories) ||
        categories.categories.length === 0) {
      fail(`knowledge package ${packageId} has no valid categories`);
    }
    const indexed = new Set();
    const categoryIds = new Set();
    const categoryMembers = new Map();
    for (const [categoryIndex, category] of categories.categories.entries()) {
      exactKeys(category, ["id", "title", "summary"],
        `knowledge package ${packageId} category ${categoryIndex}`);
      requireString(category.title,
        `knowledge package ${packageId} category ${categoryIndex} title`);
      requireString(category.summary,
        `knowledge package ${packageId} category ${categoryIndex} summary`);
      if (!ltgIdPattern.test(category.id) || categoryIds.has(category.id) ||
          (categoryIndex > 0 && categories.categories[categoryIndex - 1].id > category.id)) {
        fail(`knowledge package ${packageId} has an invalid category identifier`);
      }
      categoryIds.add(category.id);
      categoryMembers.set(category.id, new Set());
      const indexPath = `catalog/categories/${category.id}/tools.jsonl`;
      if (!packageFiles.has(indexPath)) {
        fail(`knowledge package ${packageId} is missing ${indexPath}`);
      }
      const lines = packageFiles.get(indexPath).toString("utf8").split("\n").filter(Boolean);
      const categoryEntries = new Set();
      for (const [lineIndex, line] of lines.entries()) {
        let item;
        try {
          item = JSON.parse(line);
        } catch (error) {
          fail(`${packageId}/${indexPath}:${lineIndex + 1} is invalid: ${error.message}`);
        }
        if (item === null || typeof item !== "object" || !included.includes(item.id) ||
            item.path !== `../../entries/${item.id}` || categoryEntries.has(item.id)) {
          fail(`${packageId}/${indexPath}:${lineIndex + 1} has an invalid entry reference`);
        }
        categoryEntries.add(item.id);
        categoryMembers.get(category.id).add(item.id);
        indexed.add(item.id);
      }
    }
    for (const entryId of included) {
      if (!indexed.has(entryId) ||
          !packageFiles.has(`catalog/entries/${entryId}/entry.json`) ||
          !packageFiles.has(`catalog/entries/${entryId}/README.md`)) {
        fail(`knowledge package ${packageId} entry ${entryId} is incomplete or unindexed`);
      }
      let entry;
      try {
        entry = JSON.parse(packageFiles.get(
          `catalog/entries/${entryId}/entry.json`).toString("utf8"));
      } catch (error) {
        fail(`knowledge package ${packageId} entry ${entryId} is invalid: ${error.message}`);
      }
      if (entry === null || typeof entry !== "object" || Array.isArray(entry) ||
          entry.id !== entryId) {
        fail(`knowledge package ${packageId} entry ${entryId} has the wrong identity`);
      }
      const entryCategories = requireStringArray(
        entry.categories, `knowledge package ${packageId} entry ${entryId} categories`, false);
      if (entryCategories.some((category, categoryIndex) =>
        !categoryIds.has(category) ||
        (categoryIndex > 0 && entryCategories[categoryIndex - 1] > category) ||
        !categoryMembers.get(category).has(entryId)) ||
          [...categoryMembers].some(([category, members]) =>
            members.has(entryId) && !entryCategories.includes(category))) {
        fail(`knowledge package ${packageId} entry ${entryId} has stale category indexes`);
      }
    }
    for (const entryId of excluded) {
      if ([...packageFiles.keys()].some((relative) =>
        relative.startsWith(`catalog/entries/${entryId}/`))) {
        fail(`knowledge package ${packageId} contains excluded entry ${entryId}`);
      }
    }
    for (const relative of packageFiles.keys()) {
      const categoryMatch = /^catalog\/categories\/([^/]+)\/tools\.jsonl$/.exec(relative);
      if (categoryMatch !== null && !categoryIds.has(categoryMatch[1])) {
        fail(`knowledge package ${packageId} contains unknown category ${categoryMatch[1]}`);
      }
      const entryMatch = /^catalog\/entries\/([^/]+)\/.+$/.exec(relative);
      if (entryMatch !== null && !included.includes(entryMatch[1])) {
        fail(`knowledge package ${packageId} contains unknown entry ${entryMatch[1]}`);
      }
    }
  }
  if (entries !== document.entries || excludedEntries !== document.excludedEntries) {
    fail("knowledge-task.json aggregate entry counts are inconsistent");
  }
  for (const package_ of document.packages) {
    if (package_.dependencies.some((dependency) => !packageIds.has(dependency))) {
      fail(`knowledge package ${package_.id} depends on an absent package`);
    }
  }
  const dependencyClosure = (packageId, visiting = new Set(), found = new Set()) => {
    if (found.has(packageId)) return found;
    if (visiting.has(packageId)) {
      fail(`archived knowledge dependency cycle includes ${packageId}`);
    }
    visiting.add(packageId);
    const record = document.packages.find((package_) => package_.id === packageId);
    for (const dependency of record.dependencies) {
      dependencyClosure(dependency, visiting, found);
    }
    visiting.delete(packageId);
    found.add(packageId);
    return found;
  };
  if (taskForest.packages.length !== document.packages.length) {
    fail("archived knowledge forest package count differs from the task manifest");
  }
  for (const relative of files.keys()) {
    if (relative === "forest.json") continue;
    const match = /^packages\/([^/]+)\/.+$/.exec(relative);
    if (match === null || !packageIds.has(match[1])) {
      fail(`archived knowledge contains an unmounted path: ${relative}`);
    }
  }
  for (const [index, mount] of taskForest.packages.entries()) {
    exactKeys(mount, ["id", "path"], `archived knowledge forest package ${index}`);
    if (mount.id !== document.packages[index].id || mount.path !== `packages/${mount.id}`) {
      fail("archived knowledge forest differs from the task package order");
    }
  }
  for (const package_ of document.packages) {
    const packageAllowedModules = new Set(proofKitModules);
    for (const dependencyId of dependencyClosure(package_.id)) {
      for (const moduleName of packageSources.get(dependencyId).keys()) {
        packageAllowedModules.add(moduleName);
      }
    }
    for (const [moduleName, source] of packageSources.get(package_.id)) {
      for (const imported of imports(source)) {
        const dependency = imported === "CodeLib" || imported.startsWith("CodeLib.") ||
          imported.startsWith("Init.") || imported.startsWith("Std.") ||
          imported.startsWith("Mathlib.") || imported === "Interpreter" ||
          imported.startsWith("Interpreter.");
        if (!dependency && !packageAllowedModules.has(imported)) {
          fail(`${moduleName} imports unsupported archived knowledge dependency ${imported}`);
        }
      }
    }
  }
  const allowedModules = new Set([...proofKitModules, ...leanSources.keys()]);
  return {
    manifest: structuredClone(document),
    files: new Map(files),
    leanSources,
    allowedModules,
  };
}

function validateKnowledgeEvaluation(
    document, knowledgeTask, artifactSha256, proofSourceSha256, proofTelemetry, proofSource) {
  exactKeys(document, [
    "schemaVersion", "artifactSha256", "knowledgeTaskSha256", "status", "entries", "proof",
  ], "knowledge-evaluation.json");
  if (document.schemaVersion !== 1 || document.artifactSha256 !== artifactSha256 ||
      document.knowledgeTaskSha256 !== knowledgeTask.manifest.sha256 ||
      document.status !== "accepted" || !Array.isArray(document.entries)) {
    fail("knowledge-evaluation.json has an invalid identity or status");
  }
  const allowed = new Map(knowledgeTask.manifest.packages.map((package_) => [
    package_.id, new Set(package_.entryIds),
  ]));
  const seen = new Set();
  for (const [index, entry] of document.entries.entries()) {
    exactKeys(entry, ["package", "entry", "outcome", "reason"],
      `knowledge-evaluation.json.entries[${index}]`);
    const key = `${entry.package}\0${entry.entry}`;
    if (typeof entry.package !== "string" || typeof entry.entry !== "string" ||
        !allowed.get(entry.package)?.has(entry.entry) || seen.has(key) ||
        !["used", "rejected"].includes(entry.outcome) ||
        typeof entry.reason !== "string" || entry.reason.trim().length === 0 ||
        entry.reason !== entry.reason.trim()) {
      fail(`knowledge-evaluation.json.entries[${index}] is invalid`);
    }
    if (index > 0) {
      const previous = document.entries[index - 1];
      if (`${previous.package}\0${previous.entry}` > key) {
        fail("knowledge-evaluation.json entries must be sorted by package and entry");
      }
    }
    seen.add(key);
  }
  exactKeys(document.proof, [
    "sourceSha256", "byteLength", "lineCount", "stage5Milliseconds",
  ], "knowledge-evaluation.json.proof");
  const proofBytes = Buffer.from(proofSource);
  const proofLines = proofSource === "" ? 0 :
    proofSource.split("\n").length - (proofSource.endsWith("\n") ? 1 : 0);
  if (document.proof.sourceSha256 !== proofSourceSha256 ||
      document.proof.byteLength !== proofBytes.length ||
      document.proof.lineCount !== proofLines ||
      proofTelemetry === null ||
      document.proof.stage5Milliseconds !== proofTelemetry.totalMilliseconds) {
    fail("knowledge-evaluation.json proof metrics disagree with the accepted proof");
  }
  return structuredClone(document);
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
  if (values.ltgTask !== undefined) {
    const ltgTask = validateLtgTask(
      values.ltgTask.manifest, values.ltgTask.files, values.artifact.sha256);
    writeAtomic(path.join(stageRoot, "ltg-task.json"), jsonBytes(ltgTask.manifest));
    for (const [relative, source] of ltgTask.files) {
      writeAtomic(path.join(stageRoot, "ltg", ...relative.split("/")), Buffer.from(source));
    }
  }
  if (values.knowledgeTask !== undefined) {
    if (values.ltgTask !== undefined) {
      fail("proof package cannot archive both LTG and knowledge-forest tasks");
    }
    const knowledgeTask = validateKnowledgeTask(
      values.knowledgeTask.manifest, values.knowledgeTask.files, values.artifact.sha256);
    writeAtomic(path.join(stageRoot, "knowledge-task.json"),
      jsonBytes(knowledgeTask.manifest));
    for (const [relative, source] of knowledgeTask.files) {
      writeAtomic(path.join(stageRoot, "knowledge", ...relative.split("/")),
        Buffer.from(source));
    }
    if (values.knowledgeEvaluation !== undefined) {
      const evaluation = validateKnowledgeEvaluation(
        values.knowledgeEvaluation,
        knowledgeTask,
        values.artifact.sha256,
        values.stageReports.tasks.artifactProof.sourceSha256,
        values.proofTelemetry ?? null,
        values.sources.get(values.job.behaviorModule),
      );
      writeAtomic(path.join(stageRoot, "knowledge-evaluation.json"), jsonBytes(evaluation));
    }
  } else if (values.knowledgeEvaluation !== undefined) {
    fail("knowledge evaluation requires a knowledge task");
  }
  if ((values.compilerAnnotations === undefined) !== (values.proofRecipes === undefined)) {
    fail("compiler annotations and proof recipes must appear together");
  }
  const annotated = values.compilerAnnotations !== undefined;
  const formalInterfaceVersion = values.formalInterfaceVersion ?? (annotated ? 2 : 1);
  if (![1, 2].includes(formalInterfaceVersion)) {
    fail("formal interface version must be 1 or 2");
  }
  if (!annotated && formalInterfaceVersion !== 1) {
    fail("formal interface version 2 requires an annotated package");
  }
  if (values.ltgTask !== undefined && (!annotated || formalInterfaceVersion !== 2)) {
    fail("structured LTG archival requires the annotated formal interface");
  }
  if (values.knowledgeTask !== undefined && (!annotated || formalInterfaceVersion !== 2)) {
    fail("knowledge-forest archival requires the annotated formal interface");
  }
  if (annotated) {
    writeAtomic(path.join(stageRoot, "program.annotations.json"),
      jsonBytes(values.compilerAnnotations));
    writeAtomic(path.join(stageRoot, "proof-recipes.json"),
      jsonBytes(values.proofRecipes));
  }
  writeAtomic(path.join(stageRoot, "program.wasm"), values.wasmBytes);
  installSources(path.join(stageRoot, "proof"), values.sources);
  const manifest = {
    schemaVersion: values.knowledgeTask !== undefined
      ? (values.knowledgeEvaluation === undefined ? 8 : packageSchemaVersion)
      : values.ltgTask !== undefined ? 7
        : annotated ? (formalInterfaceVersion === 2 ? 6 : 5) : 4,
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
        ![1, 2, 3, 4, 5, 6, 7, 8, 9].includes(features.extractorVersion) ||
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
        if (features.extractorVersion >= 8) functionKeys.push("fixedArrayFindIdxEqs");
        if (features.extractorVersion >= 9) functionKeys.push("fixedArrayEraseCopies");
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
            exactKeys(dispatch, features.extractorVersion >= 6
              ? ["inputLocal", "expectedSize", "encoding"]
              : ["inputLocal", "expectedSize"],
              `proof-task-features.json length dispatch ${functionIndex}:${dispatchIndex}`);
            if (![dispatch.inputLocal, dispatch.expectedSize].every(
              (value) => Number.isSafeInteger(value) && value >= 0) ||
                (features.extractorVersion >= 6 && ![
                  "eq-normalized-v1", "ne-normalized-v1", "le-unsigned-v1",
                ].includes(dispatch.encoding))) {
              fail(`proof-task-features.json length dispatch ${functionIndex}:${dispatchIndex} is invalid`);
            }
          }
        }
        if (features.extractorVersion >= 8) {
          if (!Array.isArray(function_.fixedArrayFindIdxEqs)) {
            fail(`proof-task-features.json function ${functionIndex} has invalid find-index expressions`);
          }
          for (const [findIndex, findIdx] of function_.fixedArrayFindIdxEqs.entries()) {
            exactKeys(findIdx, [
              "inputLocal", "itemLocal", "key", "resultEncoding", "scratchStart",
              "sourceWidth",
            ], `proof-task-features.json find-index expression ${functionIndex}:${findIndex}`);
            if (![findIdx.scratchStart, findIdx.sourceWidth, findIdx.inputLocal,
              findIdx.itemLocal].every((value) => Number.isSafeInteger(value) && value >= 0) ||
                findIdx.scratchStart < 2 || findIdx.sourceWidth !== 1 ||
                findIdx.inputLocal !== 0 || findIdx.itemLocal !== 1 ||
                typeof findIdx.key !== "string" || !decimalPattern.test(findIdx.key) ||
                BigInt(findIdx.key) > uint64Maximum ||
                findIdx.resultEncoding !== "none-zero-some-index-plus-one-v1") {
              fail(`proof-task-features.json find-index expression ${functionIndex}:${findIndex} is invalid`);
            }
          }
        }
        if (features.extractorVersion >= 9) {
          if (!Array.isArray(function_.fixedArrayEraseCopies)) {
            fail(`proof-task-features.json function ${functionIndex} has invalid erase copies`);
          }
          for (const [copyIndex, copy] of function_.fixedArrayEraseCopies.entries()) {
            exactKeys(copy, [
              "counterLocal", "prefixCellsLocal", "sourceLocal", "sourceWidth",
              "suffixCellsLocal", "targetLocal",
            ], `proof-task-features.json erase copy ${functionIndex}:${copyIndex}`);
            if (![copy.sourceWidth, copy.sourceLocal, copy.targetLocal,
              copy.prefixCellsLocal, copy.suffixCellsLocal, copy.counterLocal].every(
              (value) => Number.isSafeInteger(value) && value >= 0) ||
                copy.sourceWidth === 0) {
              fail(`proof-task-features.json erase copy ${functionIndex}:${copyIndex} is invalid`);
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
  let ltgTask = null;
  if (manifest.schemaVersion === 7) {
    requiredFiles.push("ltg-task.json", "ltg/README.md", "ltg/categories.json");
    const ltgRoot = path.join(packageRoot, "ltg");
    const ltgFiles = new Map(collectFiles(ltgRoot).map((relative) => [
      relative,
      fs.readFileSync(path.join(ltgRoot, ...relative.split("/"))),
    ]));
    ltgTask = validateLtgTask(JSON.parse(fs.readFileSync(
      path.join(packageRoot, "ltg-task.json"), "utf8")), ltgFiles, artifact.sha256);
  }
  let knowledgeTask = null;
  let knowledgeEvaluation = null;
  if (manifest.schemaVersion >= 8) {
    requiredFiles.push("knowledge-task.json", "knowledge/forest.json");
    const knowledgeRoot = path.join(packageRoot, "knowledge");
    const knowledgeFiles = new Map(collectFiles(knowledgeRoot).map((relative) => [
      relative,
      fs.readFileSync(path.join(knowledgeRoot, ...relative.split("/"))),
    ]));
    knowledgeTask = validateKnowledgeTask(JSON.parse(fs.readFileSync(
      path.join(packageRoot, "knowledge-task.json"), "utf8")),
    knowledgeFiles, artifact.sha256);
    if (manifest.schemaVersion >= 9) {
      requiredFiles.push("knowledge-evaluation.json");
    } else if (seen.has("knowledge-evaluation.json")) {
      fail("schema-eight package cannot contain knowledge-evaluation.json");
    }
    if (seen.has("knowledge-evaluation.json")) {
      knowledgeEvaluation = validateKnowledgeEvaluation(JSON.parse(fs.readFileSync(
        path.join(packageRoot, "knowledge-evaluation.json"), "utf8")),
      knowledgeTask, artifact.sha256, stageReports.tasks.artifactProof.sourceSha256,
      proofTelemetry, fs.readFileSync(
        path.join(packageRoot, "proof", moduleFile(job.behaviorModule)), "utf8"));
    }
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
      const allowedProofKit = proofKitModules.includes(imported) ||
        (knowledgeTask !== null && knowledgeTask.allowedModules.has(imported));
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
    ltgTask,
    knowledgeTask,
    knowledgeEvaluation,
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
  stageReportCodexVersion,
  stageReportCodexVersions,
  validateCodexTaskOutcome,
  validateLtgTask,
  validateKnowledgeTask,
  validatePackage,
  validateProofJournal,
  validateKnowledgeEvaluation,
  validateProgramImports,
  validateProofImports,
  validateStageReports,
  writeAtomic,
};
