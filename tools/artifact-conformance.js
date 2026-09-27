#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const {
  runCheckedAsync,
  spawnResultAsync,
} = require("./run-process");
const { collectReleaseInputs } = require("./artifact-identity");
const { sha256 } = require("./artifact-manifest");
const { currentLocalDate } = require("./date");
const { makeTemporaryDirectory } = require("./temp-directory");

const repoRoot = path.resolve(__dirname, "..");
const configPath = path.join(repoRoot, "proofs", "talos", "conformance.json");
const proofRoot = path.join(repoRoot, "proofs", "talos", "lean");
const codeLibRoot = path.join(
  repoRoot,
  "proofs",
  "talos",
  "lean",
  ".lake",
  "packages",
  "CodeLib",
);
const interpreterRoot = path.join(codeLibRoot, "interpreter");
const testsuiteRoot = path.join(codeLibRoot, "vendor", "testsuite");
const testsuiteExe = path.join(interpreterRoot, ".lake", "build", "bin", "testsuite");
const mathlibTacticSource = path.join(
  proofRoot,
  ".lake",
  "packages",
  "mathlib",
  "Mathlib",
  "Tactic.lean",
);
const leanrun = path.join(repoRoot, "tools", "leanrun");
const classifyFile = path.join(
  repoRoot,
  "proofs",
  "talos",
  "lean",
  "Project",
  "Artifact",
  "Binary",
  "ClassifyFile.lean",
);
const receiptPath = path.join(repoRoot, "build", "evidence", "artifact-conformance.json");

function fail(message) {
  throw new Error(message);
}

function writeReceipt(file, value) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  const temporary = `${file}.tmp-${process.pid}`;
  fs.writeFileSync(temporary, `${JSON.stringify(value, null, 2)}\n`);
  fs.renameSync(temporary, file);
}

function outputText(value) {
  if (value === undefined || value === null) return "";
  return Buffer.isBuffer(value) ? value.toString("utf8") : String(value);
}

function leanPublicImports(source) {
  const imports = [];
  let blockDepth = 0;
  for (const original of source.split("\n")) {
    let line = "";
    for (let index = 0; index < original.length;) {
      if (blockDepth === 0 && original.startsWith("--", index)) break;
      if (original.startsWith("/-", index)) {
        blockDepth += 1;
        index += 2;
      } else if (blockDepth > 0 && original.startsWith("-/", index)) {
        blockDepth -= 1;
        index += 2;
      } else {
        if (blockDepth === 0) line += original[index];
        index += 1;
      }
    }
    const match = /^\s*public\s+import\s+(.+?)\s*$/u.exec(line);
    if (match) imports.push(...match[1].split(/\s+/u));
  }
  if (blockDepth !== 0) fail("unterminated Lean block comment in import source");
  return imports;
}

function exactKeys(value, expected, description) {
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  if (actual.length !== wanted.length || actual.some((key, i) => key !== wanted[i])) {
    fail(`${description} must contain exactly: ${wanted.join(", ")}`);
  }
}

function readJson(file) {
  try {
    return JSON.parse(fs.readFileSync(file, "utf8"));
  } catch (error) {
    fail(`could not read ${file}: ${error.message}`);
  }
}

function loadConfig() {
  const config = readJson(configPath);
  exactKeys(config, [
    "schemaVersion",
    "codeLibRevision",
    "testsuiteRevision",
    "wasmtimeVersion",
    "wasmtimeWasmOptions",
    "knownIssues",
    "profileCoverageGaps",
    "validatorCases",
    "files",
  ], configPath);
  if (config.schemaVersion !== 1 || !Array.isArray(config.files) || config.files.length === 0) {
    fail(`${configPath} has an unsupported schema`);
  }
  if (!Array.isArray(config.wasmtimeWasmOptions)) {
    fail(`${configPath}: wasmtimeWasmOptions must be an array`);
  }
  const seen = new Set();
  for (const [index, entry] of config.files.entries()) {
    exactKeys(entry, ["name", "covers"], `${configPath}: files[${index}]`);
    if (!/^[A-Za-z0-9_.-]+\.wast$/.test(entry.name)) {
      fail(`${configPath}: invalid WAST filename ${JSON.stringify(entry.name)}`);
    }
    if (seen.has(entry.name)) fail(`${configPath}: duplicate WAST filename ${entry.name}`);
    if (!Array.isArray(entry.covers) || entry.covers.length === 0 ||
        entry.covers.some((item) => typeof item !== "string" || item.length === 0)) {
      fail(`${configPath}: ${entry.name} must have nonempty coverage labels`);
    }
    seen.add(entry.name);
  }
  if (!Array.isArray(config.knownIssues)) {
    fail(`${configPath}: knownIssues must be an array`);
  }
  const issueIds = new Set();
  for (const [index, issue] of config.knownIssues.entries()) {
    exactKeys(issue, ["id", "file", "scope", "document", "failures"],
      `${configPath}: knownIssues[${index}]`);
    if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(issue.id) || issueIds.has(issue.id)) {
      fail(`${configPath}: invalid or duplicate known issue id ${JSON.stringify(issue.id)}`);
    }
    if (!seen.has(issue.file)) {
      fail(`${configPath}: known issue ${issue.id} names unselected file ${issue.file}`);
    }
    if (issue.scope !== "outside-artifact-profile") {
      fail(`${configPath}: known issue ${issue.id} has unsupported scope ${JSON.stringify(issue.scope)}`);
    }
    if (typeof issue.document !== "string" || path.isAbsolute(issue.document) ||
        issue.document.split(/[\\/]/).includes("..") ||
        !fs.existsSync(path.join(repoRoot, issue.document))) {
      fail(`${configPath}: known issue ${issue.id} has invalid document path`);
    }
    if (!Array.isArray(issue.failures) || issue.failures.length === 0) {
      fail(`${configPath}: known issue ${issue.id} must name at least one failure`);
    }
    const failureKeys = new Set();
    for (const [failureIndex, failure] of issue.failures.entries()) {
      exactKeys(failure, ["line", "command", "expected", "actual"],
        `${configPath}: knownIssues[${index}].failures[${failureIndex}]`);
      if (!Number.isSafeInteger(failure.line) || failure.line <= 0 ||
          typeof failure.command !== "string" || failure.command.length === 0 ||
          typeof failure.expected !== "string" || failure.expected.length === 0 ||
          typeof failure.actual !== "string" || failure.actual.length === 0) {
        fail(`${configPath}: known issue ${issue.id} contains an invalid failure`);
      }
      const key = failureKey(failure);
      if (failureKeys.has(key)) {
        fail(`${configPath}: known issue ${issue.id} contains a duplicate failure`);
      }
      failureKeys.add(key);
    }
    issueIds.add(issue.id);
  }
  if (!Array.isArray(config.profileCoverageGaps)) {
    fail(`${configPath}: profileCoverageGaps must be an array`);
  }
  const gapFeatures = new Set();
  for (const [index, gap] of config.profileCoverageGaps.entries()) {
    exactKeys(gap, ["feature", "officialFile", "reason", "otherEvidence"],
      `${configPath}: profileCoverageGaps[${index}]`);
    if (typeof gap.feature !== "string" || gap.feature.length === 0 ||
        gapFeatures.has(gap.feature) || typeof gap.officialFile !== "string" ||
        seen.has(gap.officialFile) ||
        !/^[A-Za-z0-9_.-]+\.wast$/.test(gap.officialFile) ||
        typeof gap.reason !== "string" || gap.reason.length === 0 ||
        typeof gap.otherEvidence !== "string" || gap.otherEvidence.length === 0) {
      fail(`${configPath}: invalid or duplicate profile coverage gap at index ${index}`);
    }
    gapFeatures.add(gap.feature);
  }
  if (!Array.isArray(config.validatorCases) || config.validatorCases.length === 0) {
    fail(`${configPath}: validatorCases must be a nonempty array`);
  }
  const validatorIds = new Set();
  for (const [index, item] of config.validatorCases.entries()) {
    exactKeys(item, ["id", "file", "line", "command", "expectedStage", "expectedKind"],
      `${configPath}: validatorCases[${index}]`);
    if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(item.id) || validatorIds.has(item.id) ||
        !/^[A-Za-z0-9_.-]+\.wast$/.test(item.file) ||
        !Number.isSafeInteger(item.line) || item.line <= 0 ||
        !["assert_invalid", "assert_malformed"].includes(item.command) ||
        !["decode", "validation"].includes(item.expectedStage) ||
        typeof item.expectedKind !== "string" || item.expectedKind.length === 0) {
      fail(`${configPath}: invalid or duplicate validator case at index ${index}`);
    }
    validatorIds.add(item.id);
  }
  return config;
}

function findOnPath(name) {
  for (const directory of (process.env.PATH || "").split(path.delimiter)) {
    if (!directory) continue;
    const candidate = path.join(directory, name);
    try {
      fs.accessSync(candidate, fs.constants.X_OK);
      return candidate;
    } catch (error) {
      if (!["ENOENT", "ENOTDIR", "EACCES"].includes(error.code)) throw error;
    }
  }
  return null;
}

function requireExecutable(candidate, description) {
  try {
    fs.accessSync(candidate, fs.constants.X_OK);
    return candidate;
  } catch (error) {
    fail(`${description} is not executable at ${candidate}: ${error.message}`);
  }
}

function findWasmTools() {
  if (process.env.WASM_TOOLS) {
    return requireExecutable(path.resolve(process.env.WASM_TOOLS), "WASM_TOOLS");
  }
  const fromPath = findOnPath("wasm-tools");
  if (fromPath) return fromPath;
  return requireExecutable(
    path.join(os.homedir(), ".cargo", "bin", "wasm-tools"),
    "wasm-tools",
  );
}

function findWasmtime() {
  if (process.env.WASMTIME) {
    return requireExecutable(path.resolve(process.env.WASMTIME), "WASMTIME");
  }
  return requireExecutable(
    path.join(repoRoot, "build", "tools", "wasmtime", "current", "wasmtime"),
    "Wasmtime",
  );
}

async function checkedText(args, options = {}) {
  const result = await runCheckedAsync(args, {
    ...options,
    stdio: ["ignore", "pipe", "pipe"],
  });
  return outputText(result.stdout).trim();
}

async function checkRevision(directory, expected, description) {
  const found = await checkedText(["git", "-C", directory, "rev-parse", "HEAD"]);
  if (found !== expected) {
    fail(`${description} revision mismatch: expected ${expected}, found ${found}`);
  }
}

function requireExactFile(entries, name) {
  if (!entries.includes(name)) fail(`${name} is absent from the pinned WebAssembly testsuite`);
  return name;
}

function selectValidatorCommand(commands, item) {
  const matches = commands.filter((command) =>
    command.type === item.command && command.line === item.line);
  if (matches.length !== 1) {
    fail(`${item.file}:${item.line}: expected one ${item.command}, found ${matches.length}`);
  }
  const selected = matches[0];
  if (typeof selected.filename !== "string" ||
      path.basename(selected.filename) !== selected.filename ||
      !selected.filename.endsWith(".wasm")) {
    fail(`${item.file}:${item.line}: official command does not identify one binary module`);
  }
  return selected;
}

function parseClassifierOutput(text) {
  const results = new Map();
  for (const line of text.trim().split(/\r?\n/)) {
    if (line.length === 0) continue;
    const fields = line.split("\t");
    if (fields.length !== 3 || !["decode", "validation", "accepted"].includes(fields[1]) ||
        results.has(fields[0])) {
      fail(`could not parse artifact validator classification:\n${text.trim()}`);
    }
    results.set(fields[0], { stage: fields[1], kind: fields[2] });
  }
  return results;
}

function parseTalosCounts(text) {
  const match = text.match(
    /Totals:\s+(\d+) pass\s+(\d+) fail\s+(\d+) skip\s+(\d+) cascade\s+(\d+) decode-err\s+(\d+) interp-err\s+(\d+) out-of-fuel/,
  );
  if (!match) fail(`could not parse Talos testsuite totals:\n${text.trim()}`);
  const values = match.slice(1).map((item) => Number.parseInt(item, 10));
  return {
    pass: values[0],
    fail: values[1],
    skip: values[2],
    cascade: values[3],
    decodeError: values[4],
    interpreterError: values[5],
    outOfFuel: values[6],
  };
}

function parseTalosFailures(text) {
  const failures = [];
  for (const line of text.split(/\r?\n/)) {
    const match = line.match(
      /^\s*L(\d+)\s+(\S+)\s+Fail\s+expected (.+), got (.+)\s*$/,
    );
    if (!match) continue;
    failures.push({
      line: Number.parseInt(match[1], 10),
      command: match[2],
      expected: match[3],
      actual: match[4],
    });
  }
  return failures;
}

function failureKey(failure) {
  return JSON.stringify([
    failure.line,
    failure.command,
    failure.expected,
    failure.actual,
  ]);
}

function classifyKnownIssues(item, counts, observed, knownIssues) {
  if (counts.fail !== observed.length) {
    return {
      warnings: [],
      error: `${item.name}: Talos reported ${counts.fail} assertion failures but ` +
        `${observed.length} detailed failure rows were parsed`,
    };
  }
  if (observed.length === 0) return { warnings: [], error: null };
  const issues = knownIssues.filter((issue) => issue.file === item.name);
  const expected = issues.flatMap((issue) => issue.failures);
  const observedKeys = observed.map(failureKey).sort();
  const expectedKeys = expected.map(failureKey).sort();
  if (observedKeys.length !== expectedKeys.length ||
      observedKeys.some((key, index) => key !== expectedKeys[index])) {
    return {
      warnings: [],
      error: `${item.name}: assertion failures do not match the configured known issues`,
    };
  }
  return { warnings: issues, error: null };
}

function talosNonAssertionFailureCount(counts) {
  return counts.cascade + counts.decodeError + counts.interpreterError + counts.outOfFuel;
}

function isExpectedWasmToolsVersion(actual, expected) {
  if (actual === `wasm-tools ${expected}`) return true;
  const escaped = expected.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return new RegExp(
    `^wasm-tools ${escaped} \\([0-9a-f]{7,40} [0-9]{4}-[0-9]{2}-[0-9]{2}\\)$`,
  ).test(actual);
}

async function checkPrerequisites(config) {
  await checkRevision(codeLibRoot, config.codeLibRevision, "CodeLib");
  await checkRevision(testsuiteRoot, config.testsuiteRevision, "WebAssembly testsuite");
  const entries = fs.readdirSync(testsuiteRoot)
    .filter((entry) => entry.endsWith(".wast"));
  for (const item of config.files) requireExactFile(entries, item.name);
  for (const gap of config.profileCoverageGaps) requireExactFile(entries, gap.officialFile);
  for (const item of config.validatorCases) requireExactFile(entries, item.file);

  const wasmTools = findWasmTools();
  const expectedWasmTools = fs.readFileSync(
    path.join(repoRoot, ".wasm-tools-version"),
    "utf8",
  ).trim();
  const wasmToolsVersion = await checkedText([wasmTools, "--version"]);
  if (!isExpectedWasmToolsVersion(wasmToolsVersion, expectedWasmTools)) {
    fail(`wasm-tools version mismatch: expected ${expectedWasmTools}, found ${wasmToolsVersion}`);
  }

  const wasmtime = findWasmtime();
  const wasmtimeVersion = await checkedText([wasmtime, "--version"]);
  if (!wasmtimeVersion.startsWith(`wasmtime ${config.wasmtimeVersion} `)) {
    fail(`Wasmtime version mismatch: expected ${config.wasmtimeVersion}, found ${wasmtimeVersion}`);
  }
  return { wasmTools, wasmtime };
}

async function buildTestsuite() {
  const tacticImports = leanPublicImports(fs.readFileSync(mathlibTacticSource, "utf8"));
  if (tacticImports.length === 0 || new Set(tacticImports).size !== tacticImports.length) {
    fail(`${mathlibTacticSource}: expected distinct public imports`);
  }
  const chunkSize = 16;
  for (let index = 0; index < tacticImports.length; index += chunkSize) {
    await runCheckedAsync([
      leanrun,
      "--timeout", "30m",
      "lake", "-d", interpreterRoot, "build",
      ...tacticImports.slice(index, index + chunkSize),
    ], { cwd: repoRoot, env: process.env, stdio: "inherit" });
  }
  await runCheckedAsync([
    leanrun,
    "--timeout", "30m",
    "lake", "-d", interpreterRoot, "build", "Interpreter.Testsuite.Exec",
  ], { cwd: repoRoot, env: process.env, stdio: "inherit" });
  await runCheckedAsync([
    leanrun,
    "--timeout", "30m",
    "lake", "-d", interpreterRoot, "build", "testsuite",
  ], { cwd: repoRoot, env: process.env, stdio: "inherit" });
}

async function checkArtifactValidator(config, wasmTools) {
  const temporaryRoot = makeTemporaryDirectory("leanexe-validator-");
  try {
    const groups = new Map();
    for (const item of config.validatorCases) {
      if (!groups.has(item.file)) groups.set(item.file, []);
      groups.get(item.file).push(item);
    }
    const staged = [];
    for (const [file, items] of groups) {
      const fileRoot = path.join(temporaryRoot, path.basename(file, ".wast"));
      const moduleRoot = path.join(fileRoot, "modules");
      const jsonPath = path.join(fileRoot, "commands.json");
      fs.mkdirSync(moduleRoot, { recursive: true });
      await runCheckedAsync([
        wasmTools,
        "json-from-wast",
        path.join(testsuiteRoot, file),
        "--wasm-dir", moduleRoot,
        "-o", jsonPath,
      ], { cwd: repoRoot, env: process.env, stdio: "inherit" });
      const commands = readJson(jsonPath).commands;
      if (!Array.isArray(commands)) fail(`${file}: wasm-tools emitted no command array`);
      for (const item of items) {
        const command = selectValidatorCommand(commands, item);
        const source = path.join(moduleRoot, command.filename);
        const target = path.join(temporaryRoot, `${item.id}.wasm`);
        if (item.command === "assert_invalid") {
          await runCheckedAsync([
            wasmTools, "strip", "--all", source, "-o", target,
          ], { cwd: repoRoot, env: process.env, stdio: "inherit" });
        } else {
          fs.copyFileSync(source, target);
        }
        staged.push({ item, target });
      }
    }
    await runCheckedAsync([
      leanrun,
      "--timeout", "15m",
      "lake", "-d", proofRoot, "build", "Project.Artifact.Binary.ClassifyFile",
    ], { cwd: repoRoot, env: process.env, stdio: "inherit" });
    const output = await checkedText([
      leanrun,
      "--timeout", "15m",
      "lake", "-d", proofRoot, "env", "lean", "--run", classifyFile,
      ...staged.map((entry) => entry.target),
    ], { cwd: repoRoot, env: process.env });
    const classified = parseClassifierOutput(output);
    const failures = [];
    for (const { item, target } of staged) {
      const found = classified.get(target);
      if (!found) {
        failures.push(`${item.id}: artifact validator returned no classification`);
        continue;
      }
      console.log(`${item.id}: artifact validator ${found.stage} ${found.kind}`);
      if (found.stage !== item.expectedStage || found.kind !== item.expectedKind) {
        failures.push(
          `${item.id}: expected ${item.expectedStage} ${item.expectedKind}, ` +
          `found ${found.stage} ${found.kind}`,
        );
      }
    }
    if (classified.size !== staged.length) {
      failures.push(
        `artifact validator returned ${classified.size} classifications for ${staged.length} cases`,
      );
    }
    if (failures.length > 0) {
      fail(`official artifact-validator gate failed:\n${failures.join("\n")}`);
    }
    return staged.length;
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true, force: true });
  }
}

async function runTalos(item, wasmTools) {
  const env = {
    ...process.env,
    PATH: `${path.dirname(wasmTools)}${path.delimiter}${process.env.PATH || ""}`,
  };
  const temporaryRoot = makeTemporaryDirectory("leanexe-wast-");
  const stagedTestsuite = path.join(temporaryRoot, "vendor", "testsuite");
  fs.mkdirSync(stagedTestsuite, { recursive: true });
  fs.copyFileSync(
    path.join(testsuiteRoot, item.name),
    path.join(stagedTestsuite, item.name),
  );
  let result;
  try {
    result = await spawnResultAsync([
      leanrun,
      "--timeout", "10m",
      testsuiteExe,
    ], {
      cwd: temporaryRoot,
      env,
      stdio: ["ignore", "pipe", "pipe"],
    });
  } finally {
    fs.rmSync(temporaryRoot, { recursive: true, force: true });
  }
  const stdout = outputText(result.stdout);
  const stderr = outputText(result.stderr);
  const detail = `${stdout}\n${stderr}`;
  const counts = parseTalosCounts(detail);
  const failures = parseTalosFailures(detail);
  if (result.signal) fail(`${item.name}: Talos terminated by ${result.signal}`);
  if (result.status !== 0 && result.status !== 1) {
    fail(`${item.name}: Talos exited with status ${result.status}:\n${stderr.trim()}`);
  }
  return { counts, failures, detail: detail.trim() };
}

async function runWasmtime(item, config, wasmtime) {
  const args = ["timeout", "5m", wasmtime, "wast"];
  for (const option of config.wasmtimeWasmOptions) args.push("-W", option);
  args.push(path.join(testsuiteRoot, item.name));
  return spawnResultAsync(args, {
    cwd: repoRoot,
    env: process.env,
    stdio: ["ignore", "pipe", "pipe"],
  });
}

async function check() {
  const config = loadConfig();
  const { wasmTools, wasmtime } = await checkPrerequisites(config);
  const validatorCaseCount = await checkArtifactValidator(config, wasmTools);
  await buildTestsuite();
  const failures = [];
  const warnings = [];
  const totals = {
    pass: 0,
    fail: 0,
    skip: 0,
    cascade: 0,
    decodeError: 0,
    interpreterError: 0,
    outOfFuel: 0,
  };
  let wasmtimeFilesPassed = 0;
  for (const item of config.files) {
    const talos = await runTalos(item, wasmTools);
    const wasmtimeResult = await runWasmtime(item, config, wasmtime);
    const counts = talos.counts;
    const wasmtimePassed = wasmtimeResult.status === 0 && !wasmtimeResult.signal;
    for (const key of Object.keys(totals)) totals[key] += counts[key];
    if (wasmtimePassed) wasmtimeFilesPassed += 1;
    console.log(
      `${item.name}: Talos ${counts.pass} pass, ${counts.fail} fail, ${counts.skip} skip, ` +
      `${counts.decodeError} decode error, ${counts.interpreterError} interpreter error, ` +
      `${counts.outOfFuel} out of fuel, ${counts.cascade} cascade; ` +
      `Wasmtime ${wasmtimePassed ? "pass" : "fail"}`,
    );
    if (talosNonAssertionFailureCount(counts) > 0) {
      failures.push(`${item.name}: Talos reported non-assertion failures\n${talos.detail}`);
    }
    const known = classifyKnownIssues(item, counts, talos.failures, config.knownIssues);
    if (known.error) {
      failures.push(`${known.error}\n${talos.detail}`);
    } else {
      warnings.push(...known.warnings);
    }
    if (!wasmtimePassed) {
      const detail = [
        outputText(wasmtimeResult.stderr).trim(),
        outputText(wasmtimeResult.stdout).trim(),
      ].filter(Boolean).join("\n");
      failures.push(`${item.name}: Wasmtime failed${detail ? `\n${detail}` : ""}`);
    }
  }
  if (failures.length > 0) {
    fail(`conformance gate failed:\n${failures.join("\n")}`);
  }
  for (const issue of warnings) {
    console.log(
      `${issue.file}: warning: ${issue.id} matched ${issue.failures.length} known ` +
      `upstream assertion failures outside the artifact profile; see ${issue.document}`,
    );
  }
  const warningSuffix = warnings.length === 0
    ? ""
    : ` with ${warnings.length} known upstream warning${warnings.length === 1 ? "" : "s"}`;
  console.log(
    `Artifact semantic and validator conformance passed${warningSuffix}: ` +
    `${config.files.length} official execution files, ${validatorCaseCount} official invalid modules`,
  );
  const receipt = {
    schemaVersion: 1,
    date: currentLocalDate(),
    result: warnings.length === 0 ? "passed" : "passed-with-warning",
    configSha256: sha256(fs.readFileSync(configPath)),
    releaseInputSha256: collectReleaseInputs(repoRoot).sha256,
    officialFileCount: config.files.length,
    officialValidatorCases: validatorCaseCount,
    talos: totals,
    wasmtimeFilesPassed,
    warnings: [...new Set(warnings.map((issue) => issue.id))],
  };
  writeReceipt(receiptPath, receipt);
  console.log(`CONFORMANCE_RECEIPT ${JSON.stringify(receipt)}`);
  return receipt;
}

async function main() {
  if (process.argv.length !== 3 || process.argv[2] !== "check") {
    fail("usage: artifact-conformance.js check");
  }
  await check();
}

if (require.main === module) {
  main().catch((error) => {
    console.error(`artifact-conformance.js: ${error.message}`);
    process.exitCode = 1;
  });
}

module.exports = {
  mathlibTacticSource,
  classifyKnownIssues,
  isExpectedWasmToolsVersion,
  leanPublicImports,
  parseTalosCounts,
  parseTalosFailures,
  parseClassifierOutput,
  requireExactFile,
  selectValidatorCommand,
};
