"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { spawnSync } = require("node:child_process");
const { isDeepStrictEqual } = require("node:util");
const { spawnResultAsync } = require("../run-process");

const root = path.resolve(__dirname, "../..");
const proofRoot = path.join(root, "proofs/talos/lean");
const runner = path.join(root, "tools/leanrun");
const digest = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const write = (file, value) => fs.writeFileSync(file, value, { flag: "wx" });
const writeJson = (file, value) => write(file, JSON.stringify(value, null, 2) + "\n");
const requireThat = (condition, message) => { if (!condition) throw new Error(message); };
const allowedAxioms = new Set(["propext", "Classical.choice", "Quot.sound"]);

async function lean(stage, args, log) {
  console.log(`WGSL ${stage}`);
  const result = await spawnResultAsync([runner, "--timeout", "120s", ...args], {
    cwd: root, env: process.env, stdio: ["ignore", "pipe", "pipe"],
  });
  const output = result.stdout.toString("utf8") + result.stderr.toString("utf8");
  write(log, output);
  requireThat(result.status === 0, `${stage} failed; retained diagnostics: ${log}`);
  requireThat(!/\bsorryAx\b/.test(output), `${stage} uses sorryAx; see ${log}`);
  return output;
}

function audit(output, names = ["package", "artifact", "numerical", "numericalWide", "exact"].map(n => `CheckedWGSLPackage.${n}`)) {
  const expected = new Set(names);
  const checked = {};
  for (const match of output.matchAll(/'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)/g)) {
    const [, name, list = ""] = match;
    requireThat(expected.delete(name), `unexpected or duplicate axiom report: ${name}`);
    checked[name] = list.split(",").map(s => s.trim()).filter(Boolean);
    for (const axiom of checked[name]) requireThat(allowedAxioms.has(axiom), `unsupported axiom: ${axiom}`);
  }
  requireThat(expected.size === 0, `missing axiom reports: ${[...expected]}`);
  return checked;
}

async function checkPackage(directory, { wordsOnly = false } = {}) {
  directory = path.resolve(directory);
  const checks = path.join(root, "build/wgsl/package-checks");
  fs.mkdirSync(checks, { recursive: true });
  const attempt = fs.mkdtempSync(path.join(checks, "check-"));
  try {
    const shader = fs.readFileSync(path.join(directory, "kernel.wgsl"));
    const manifest = fs.readFileSync(path.join(directory, "manifest.json"));
    requireThat(shader.length <= 65536 && manifest.length <= 65536, "verification input exceeds 64 KiB");
    const shaderPath = path.join(attempt, "kernel.wgsl");
    const manifestPath = path.join(attempt, "manifest.json");
    const proof = path.join(attempt, "Proof.lean");
    write(shaderPath, shader);
    write(manifestPath, manifest);
    await lean("shared proof dependencies", ["lake", "-d", proofRoot, "build",
      wordsOnly ? "Project.WGSL.ExecutionPackage" : "Project.WGSL.Package"],
      path.join(attempt, "dependencies.log"));
    await lean("prepare independent proof", ["lake", "env", "lean", "--run",
      path.join(__dirname, "Prepare.lean"), shaderPath, manifestPath, proof, ...(wordsOnly ? ["words"] : [])], path.join(attempt, "prepare.log"));
    const output = await lean("kernel and exact file checks", ["lake", "-d", proofRoot, "env", "lean",
      "--run", proof, shaderPath, manifestPath], path.join(attempt, "verify.log"));
    const axioms = wordsOnly ? audit(output, ["package", "artifact", "exact"].map(n => `CheckedWGSLPackage.${n}`)) : audit(output);
    const bindings = output.split("\n").filter(line => line.startsWith("WGSL_PACKAGE_BINDING "));
    requireThat(bindings.length === 1, "missing or duplicate checked manifest binding");
    const metadata = JSON.parse(bindings[0].slice("WGSL_PACKAGE_BINDING ".length));
    requireThat(isDeepStrictEqual(metadata, JSON.parse(manifest.toString("utf8"))),
      "manifest interpretation differs from the Lean-checked metadata (including extra fields)");
    requireThat(fs.readFileSync(shaderPath).equals(shader) && fs.readFileSync(manifestPath).equals(manifest),
      "verification snapshot changed during checking");
    const receipt = {
      schemaVersion: 1, status: "pass", shaderSha256: digest(shader), manifestSha256: digest(manifest),
      proofSha256: digest(fs.readFileSync(proof)), profile: metadata.profile, axioms,
      subject: "Exact embedded WGSL source with parsed configuration and matched manifest fields",
      claims: ["termination", "memory safety", "GEMM correspondence", ...(wordsOnly ? [] : ["conditional numerical bound"])],
      exactness: metadata.profile.id === "leanexe-f32-rne-separate-v1" ? "separate binary32 GEMM" : "not claimed for fusion profile",
      ...(wordsOnly ? { wordSemanticsOnly: true, realReferenceRequired: false, numericalErrorTolerance: null } : {
        numericalDomain: "Project.WGSL.Binary32.DotDomain; per-cell absolute error <= 2*K*2^-23",
        wideNumericalDomain: "Project.WGSL.Binary32.WideDotDomain; per-cell absolute error <= K*stepError(accBudget, productBudget)",
      }),
      runtimeConformanceEstablished: false,
      boundary: "JSON decoding and byte-to-file comparison are checker operations; the kernel checks shader parsing and typed metadata agreement.",
    };
    writeJson(path.join(attempt, "verification.json"), receipt);
    console.log(`WGSL package verified: ${attempt}`);
    return { directory, attempt, shader, manifest, metadata, receipt, shaderPath, manifestPath };
  } catch (error) {
    writeJson(path.join(attempt, "failure.json"), { status: "error", error: error.message });
    throw error;
  }
}

function executeChecked(checked) {
  const report = path.join(checked.attempt, "execution.json");
  const args = [checked.shaderPath, checked.manifestPath, "--snapshot-stdin", "--report", report];
  let command;
  if (process.platform === "darwin") {
    command = path.join(__dirname, "run-macos-cpu.sh");
  } else {
    command = process.env.LEANEXE_WGPU_PYTHON || "python3";
    args.unshift(path.join(__dirname, "run.py"));
    args.push("--backend", process.env.WGPU_BACKEND_TYPE || "Vulkan", "--adapter",
      process.env.LEANEXE_WGPU_ADAPTER || "llvmpipe");
  }
  console.log("WGSL execute the checked input snapshot on the CPU");
  const result = spawnSync(command, args, { cwd: root, env: process.env, encoding: "utf8", timeout: 45000,
    input: JSON.stringify({ artifactUtf8: checked.shader.toString("utf8"), manifestUtf8: checked.manifest.toString("utf8") }),
  });
  write(path.join(checked.attempt, "execution.log"), (result.stdout || "") + (result.stderr || ""));
  requireThat(!result.error && result.status === 0, `CPU execution failed; evidence retained at ${report}`);
  const evidence = JSON.parse(fs.readFileSync(report, "utf8"));
  requireThat(evidence.status === "pass" && Buffer.from(evidence.artifact.text, "utf8").equals(checked.shader) &&
    isDeepStrictEqual(evidence.manifest, checked.metadata) && evidence.manifestSha256 === digest(checked.manifest),
    "native evidence does not identify the verified input snapshot");
  console.log(`WGSL verified execution passed: ${evidence.check.checkedElements} outputs; ${report}`);
  return report;
}

async function generate(directory, dimensions) {
  directory = path.resolve(directory);
  requireThat(dimensions.length === 4 && dimensions.slice(0, 3).every(s => /^[1-9][0-9]*$/.test(s)) &&
    ["separate", "fusion"].includes(dimensions[3]), "expected ROWS COLS INNER separate|fusion");
  fs.mkdirSync(path.dirname(directory), { recursive: true });
  fs.mkdirSync(directory); // Fresh package only: retain all earlier output.
  await lean("generate supported Lean GEMM candidate", ["lake", "env", "lean", "--run",
    path.join(__dirname, "Generate.lean"), directory, ...dimensions], path.join(directory, "generate.log"));
  return directory;
}

async function corpus(directory, { wordsOnly = false } = {}) {
  directory = path.resolve(directory);
  fs.mkdirSync(path.dirname(directory), { recursive: true });
  fs.mkdirSync(directory);
  const cases = JSON.parse(fs.readFileSync(path.join(__dirname, "corpus.json"), "utf8"));
  const results = [];
  for (const item of cases.positive) {
    const selected = path.join(directory, item.name);
    await generate(selected, item.dimensions);
    const checked = await checkPackage(selected, { wordsOnly });
    const execution = wordsOnly ? null : executeChecked(checked);
    results.push({ name: item.name, status: "pass", verification: path.join(checked.attempt, "verification.json"), execution });
  }
  const base = path.join(directory, "rectangular");
  for (const item of cases.negative) {
    const selected = path.join(directory, item.name);
    fs.mkdirSync(selected);
    let shader = fs.readFileSync(path.join(base, "kernel.wgsl"), "utf8");
    const manifest = JSON.parse(fs.readFileSync(path.join(base, "manifest.json"), "utf8"));
    if (item.shaderReplace) shader = shader.replace(...item.shaderReplace);
    if (item.manifestRows) manifest.dimensions.rows = item.manifestRows;
    if (item.extraMetadata) manifest.unverifiedExtraField = true;
    write(path.join(selected, "kernel.wgsl"), shader);
    writeJson(path.join(selected, "manifest.json"), manifest);
    let failure;
    try { await checkPackage(selected, { wordsOnly }); } catch (error) { failure = error.message; }
    requireThat(failure && failure.includes(item.failure), `negative case ${item.name} did not fail as expected: ${failure}`);
    results.push({ name: item.name, status: "rejected", failure });
  }
  writeJson(path.join(directory, "corpus.json"), { status: "pass", results });
  console.log(`WGSL corpus passed: ${results.length} cases; ${directory}`);
}

async function main(args) {
  const [command, directory, ...rest] = args;
  requireThat(directory, "expected a WGSL package directory");
  if (command === "wgsl-gpt2-check") {
    requireThat(rest.length === 0, "unexpected arguments");
    return require("./gpt2/check").check(directory);
  }
  if (command === "wgsl-word-check") {
    requireThat(rest.length === 0, "unexpected arguments");
    return checkPackage(directory, { wordsOnly: true });
  }
  if (command.startsWith("wgsl-gpt128-")) {
    await require("./gpt128").main([command, directory, ...rest]);
    return;
  }
  if (command.startsWith("wgsl-float-")) {
    await require("./float").main([command, directory, ...rest]);
    return;
  }
  if (command.startsWith("wgsl-gpt-")) {
    await require("./gpt").main([command, directory, ...rest]);
  } else if (command.startsWith("wgsl-bundle-")) {
    return require("./bundle").main(args);
  } else if (command === "wgsl-corpus" || command === "wgsl-word-corpus") {
    requireThat(rest.length === 0, "unexpected arguments");
    await corpus(directory, { wordsOnly: command === "wgsl-word-corpus" });
  } else if (command === "wgsl-build") {
    await generate(directory, rest);
    executeChecked(await checkPackage(directory));
  } else if (command === "wgsl-check" || command === "wgsl-run") {
    requireThat(rest.length === 0, "unexpected arguments");
    const checked = await checkPackage(directory);
    if (command === "wgsl-run") executeChecked(checked);
  } else throw new Error(`unknown WGSL command: ${command}`);
}

module.exports = { main, checkPackage, executeChecked, generate, audit, lean };
