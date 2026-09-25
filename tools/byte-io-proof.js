#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const assert = require("node:assert/strict");
const { runChecked } = require("./run-process");
const { certificates } = require("./byte-io-kernel");

const root = path.resolve(__dirname, "..");
const proofRoot = path.join(root, "proofs/talos/lean");
const moduleRoot = path.join(proofRoot, "Project/ByteIO");
const fixture = path.join(root, "proofs/byte-io/echo.wasm");
const targets = [
  "Protocol", "Wasi", "Binary", "ArtifactByteLookup", "ArtifactSections",
  "ArtifactCode0", "ArtifactCode1", "ArtifactCode2", "ArtifactCode3", "ArtifactCode4",
  "ArtifactCode5", "ArtifactSection10", "ArtifactDecode", "ArtifactValidation",
  "ValidationChecks", "Artifact", "Execution", "ExecutionEof", "ExecutionBroken",
  "ExecutionTimeout", "ExecutionRetry", "ExecutionCases", "ExecutionStart", "Verification",
];
const theoremNames = [
  "Protocol.deadline_bounded", "Protocol.deadline_no_wrap",
  "Protocol.emitted_prefix", "Protocol.successful_write_exact",
  "Protocol.writeStep_deadline", "Protocol.observe_continues_before_deadline",
  "Protocol.write_terminates", "commitRead_conserves", "commitRead_at",
  "commitRead_frame", "commitWrite_frame", "commitWrite_exact",
  "commitRead_resources", "commitWrite_resources", "fdRead_contract", "fdWrite_contract",
  "flagsUpdate_nonblocking", "clockCall_contract", "pollCall_contract",
  "pollTime_monotone", "pollEvents_count", "poll_before_deadline_ready",
  "commitPoll_frame", "exit_records_status", "wasiEnv_satisfies",
  "Binary.decode_sound", "Binary.validate_sound", "Artifact.decoded",
  "Artifact.encoded", "Artifact.validated", "Artifact.valid",
  "Artifact.imports_exact", "Artifact.exports_exact", "partialHost_satisfies",
  "echo_partial_writes", "echo_eof", "echo_broken_prefix", "echo_poll_timeout", "echo_retry_ready",
  "brokenHost_satisfies", "timeoutHost_satisfies", "retryHost_satisfies", "ValidationChecks.rejects_missing_import_type",
  "ValidationChecks.rejects_export_past_end", "exits_of_check", "echo_start_exits",
].map(name => `Project.ByteIO.${name}`);

function embeddedSource(bytes, {
  project = "ByteIO", fixturePath = "proofs/byte-io/echo.wasm", entry = "LeanExe.Examples.ByteIO.echo",
  generator = "tools/byte-io-proof.js",
} = {}) {
  const hash = crypto.createHash("sha256").update(bytes).digest("hex");
  const rows = [];
  for (let i = 0; i < bytes.length; i += 24) rows.push(`  ${[...bytes.subarray(i, i + 24)].join(", ")}`);
  const depth = bytes.length > 4096 ? "set_option maxRecDepth 131072\n\n" : "";
  return `/-!\nGenerated from \`${fixturePath}\`; checked by \`${generator}\`.\nSource: \`${entry}\`.\nSHA-256: ${hash}\n-/\nnamespace Project.${project}.Artifact\n\n${depth}def bytes : ByteArray := ByteArray.mk #[\n${rows.join(",\n")}\n]\n\nend Project.${project}.Artifact\n`;
}

function byteLookupSource(bytes, project = "ByteIO") {
  const declarations = [];
  function split(lo, hi) {
    const name = `bytes_${lo}_${hi}`;
    if (hi - lo <= 128) {
      declarations.push(`def ${name} : List UInt8 :=\n  [${[...bytes.subarray(lo, hi)].join(", ")}]\n\ntheorem ${name}_length : ${name}.length = ${hi - lo} := rfl`);
    } else {
      const mid = Math.floor((lo + hi) / 2), left = split(lo, mid), right = split(mid, hi);
      declarations.push(`@[cbv_opaque] def ${name} : List UInt8 := ${left} ++ ${right}
theorem ${name}_length : ${name}.length = ${hi - lo} := by
  change (${left} ++ ${right}).length = _
  rw [List.length_append, ${left}_length, ${right}_length]
@[cbv_eval] theorem ${name}_get (i : Nat) :
    ${name}[i]? = if i < ${mid - lo} then ${left}[i]? else ${right}[i - ${mid - lo}]? := by
  change (${left} ++ ${right})[i]? = _
  rw [List.getElem?_append, ${left}_length]`);
    }
    return name;
  }
  const tree = split(0, bytes.length);
  return `import Project.${project}.ArtifactBytes
import Project.Artifact.Binary.Evaluate

namespace Project.${project}.Artifact.ByteLookup

set_option maxRecDepth 131072

@[cbv_opaque] def data : Array UInt8 := bytes.data
@[cbv_eval] theorem bytes_data : bytes.data = data := rfl
@[cbv_eval] theorem bytes_size : bytes.size = ${bytes.length} := rfl

${declarations.join("\n\n")}

set_option maxRecDepth 131072 in
theorem data_eq : data.toList = ${tree} := by rfl
@[cbv_eval] theorem data_get (i : Nat) : data[i]? = ${tree}[i]? := by
  rw [← Array.getElem?_toList, data_eq]
@[cbv_eval] theorem data_size : data.size = ${bytes.length} := rfl

#print axioms data_get
end Project.${project}.Artifact.ByteLookup
`;
}

function auditAxioms(output, expected = theoremNames) {
  const allowed = new Set(["propext", "Classical.choice", "Quot.sound"]);
  const reports = [...output.matchAll(/'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)/g)];
  assert.equal(reports.length, expected.length, "missing or extra axiom reports");
  assert.deepEqual(reports.map(report => report[1]).sort(), [...expected].sort(), "theorem audit mismatch");
  for (const report of reports) {
    for (const name of (report[2] || "").split(",").map(x => x.trim()).filter(Boolean)) {
      assert.ok(allowed.has(name), `unsupported axiom: ${name}`);
    }
  }
}

function lean(args, options = {}) {
  return runChecked(["lake", "-d", proofRoot, ...args], {
    cwd: root, timeout: 5 * 60 * 1000, ...options,
  });
}

function compileCurrent() {
  const outputDir = path.join(root, ".lake/build/byte-io-proof");
  fs.mkdirSync(outputDir, { recursive: true });
  runChecked(["lake", "build", "lean-wasm", "LeanExe.Examples.ByteIO"], {
    cwd: root, stdio: "inherit", timeout: 15 * 60 * 1000,
  });
  const fresh = path.join(outputDir, "echo.wasm");
  runChecked([process.env.LEAN_WASM_EXE || path.join(root, ".lake/build/bin/lean-wasm"),
    "compile-wasi-io", "--module", "LeanExe.Examples.ByteIO", "--entry", "LeanExe.Examples.ByteIO.echo",
    "--out", fresh], { cwd: root, timeout: 60 * 1000 });
  runChecked([process.env.WASM_TOOLS || "wasm-tools", "validate", fresh], { cwd: root });
  return fresh;
}

function prepare() {
  const fresh = compileCurrent();
  const bytes = fs.readFileSync(fresh);
  fs.copyFileSync(fresh, fixture);
  fs.writeFileSync(path.join(moduleRoot, "ArtifactBytes.lean"), embeddedSource(bytes));
  fs.writeFileSync(path.join(moduleRoot, "ArtifactByteLookup.lean"), byteLookupSource(bytes));
  lean(["build", "Project.ByteIO.Binary", "Project.ByteIO.ArtifactBytes"], { stdio: "inherit" });
  const generated = lean(["env", "lean", "--run", path.join(moduleRoot, "GenerateCache.lean")],
    { encoding: "utf8", maxBuffer: 16 * 1024 * 1024 });
  assert.ok(generated.stdout.startsWith("import Project.ByteIO.Binary\n"), "invalid generated cache");
  fs.writeFileSync(path.join(moduleRoot, "ArtifactCache.lean"), generated.stdout);
  const metadata = lean(["env", "lean", "--run",
    path.join(proofRoot, "Project/Artifact/Binary/CodeOffsets.lean"), fixture, "--nested"],
    { encoding: "utf8", maxBuffer: 16 * 1024 * 1024 });
  for (const [name, source] of certificates(bytes, metadata.stdout)) {
    fs.writeFileSync(path.join(moduleRoot, `${name}.lean`), source);
  }
  console.log("Byte-I/O caches prepared; run check to prove the refreshed bytes");
}

function check() {
  const fresh = compileCurrent();
  const outputDir = path.dirname(fresh);
  const bytes = fs.readFileSync(fixture);
  assert.ok(fs.readFileSync(fresh).equals(bytes), "echo proof fixture differs from current compiler output");
  assert.equal(fs.readFileSync(path.join(moduleRoot, "ArtifactBytes.lean"), "utf8"),
    embeddedSource(bytes), "embedded echo bytes are stale");
  assert.equal(fs.readFileSync(path.join(moduleRoot, "ArtifactByteLookup.lean"), "utf8"),
    byteLookupSource(bytes), "byte lookup proofs are stale");
  for (const target of targets) lean(["build", `Project.ByteIO.${target}`], { stdio: "inherit" });
  const audit = path.join(outputDir, "Audit.lean");
  fs.writeFileSync(audit, [
    "import Project.ByteIO.Verification", "",
    ...theoremNames.map(name => `#print axioms ${name}`), "",
  ].join("\n"));
  const result = lean(["env", "lean", audit], { encoding: "utf8", maxBuffer: 16 * 1024 * 1024 });
  auditAxioms(result.stdout);
  process.stdout.write(result.stdout);
  console.log(`Byte-I/O proof passed: exact echo bytes and ${theoremNames.length} standard-axiom theorem audits`);
}

if (require.main === module) {
  if (process.argv.length !== 3 || !["check", "prepare"].includes(process.argv[2])) {
    console.error("usage: tools/byte-io-proof.js <check | prepare>");
    process.exit(2);
  }
  try { if (process.argv[2] === "prepare") prepare(); else check(); }
  catch (error) { console.error(`byte-io-proof.js: ${error.message}`); process.exit(1); }
}
module.exports = { embeddedSource, byteLookupSource, auditAxioms };
