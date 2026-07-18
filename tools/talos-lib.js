"use strict";

const childProcess = require("node:child_process");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");

const repoRoot = path.resolve(__dirname, "..");
const talosRoot = path.join(repoRoot, "proofs", "talos");
const proofRoot = path.join(talosRoot, "lean");
const registryPath = path.join(talosRoot, "cases.json");
const generatedRoot = path.join(talosRoot, ".generated");
const leanWasm = path.join(repoRoot, ".lake", "build", "bin", "lean-wasm");
const codeLibRoot = path.join(
  proofRoot,
  ".lake",
  "packages",
  "CodeLib",
);
const verifierRoot = path.join(codeLibRoot, "verifier");
const verifier = path.join(
  verifierRoot,
  ".lake",
  "build",
  "bin",
  "verifier",
);

const limitedPrefix = [
  "--user",
  "--scope",
  "--quiet",
  "--collect",
  "-p",
  "MemoryHigh=4G",
  "-p",
  "MemoryMax=6G",
  "-p",
  "MemorySwapMax=1G",
  "-p",
  "CPUQuota=100%",
  "nice",
  "-n",
  "10",
  "ionice",
  "-c",
  "3",
];

function run(stage, command, args, options = {}) {
  const result = childProcess.spawnSync(command, args, {
    cwd: options.cwd,
    env: options.env || process.env,
    stdio: "inherit",
  });
  if (result.error) {
    throw new Error(`${stage}: could not run ${command}: ${result.error.message}`);
  }
  if (result.status !== 0) {
    const outcome = result.signal
      ? `signal ${result.signal}`
      : `exit status ${result.status}`;
    throw new Error(`${stage}: ${command} failed with ${outcome}`);
  }
}

function runLimited(stage, timeout, command, args, cwd) {
  run(
    stage,
    "systemd-run",
    [...limitedPrefix, "timeout", timeout, command, ...args],
    { cwd },
  );
}

function expectedKeys(value, keys, description) {
  const actual = Object.keys(value).sort();
  const expected = [...keys].sort();
  if (actual.length !== expected.length || actual.some((key, i) => key !== expected[i])) {
    throw new Error(
      `${description} must contain exactly these fields: ${expected.join(", ")}`,
    );
  }
}

function snakeToPascal(name) {
  return name
    .split("_")
    .map((part) => part[0].toUpperCase() + part.slice(1))
    .join("");
}

function loadRegistry() {
  let registry;
  try {
    registry = JSON.parse(fs.readFileSync(registryPath, "utf8"));
  } catch (error) {
    throw new Error(`could not read ${registryPath}: ${error.message}`);
  }
  if (!registry || typeof registry !== "object" || Array.isArray(registry)) {
    throw new Error(`${registryPath} must contain an object`);
  }
  expectedKeys(registry, ["version", "cases"], registryPath);
  if (registry.version !== 1) {
    throw new Error(`${registryPath} has unsupported version ${registry.version}`);
  }
  if (!Array.isArray(registry.cases) || registry.cases.length === 0) {
    throw new Error(`${registryPath}: cases must be a nonempty array`);
  }

  const names = new Set();
  const leanModules = new Set();
  for (const [index, item] of registry.cases.entries()) {
    const description = `${registryPath}: cases[${index}]`;
    if (!item || typeof item !== "object" || Array.isArray(item)) {
      throw new Error(`${description} must be an object`);
    }
    expectedKeys(
      item,
      ["name", "module", "entry", "leanModule", "specTarget", "complete"],
      description,
    );
    for (const field of ["name", "module", "entry", "leanModule", "specTarget"]) {
      if (typeof item[field] !== "string" || item[field].length === 0) {
        throw new Error(`${description}.${field} must be a nonempty string`);
      }
    }
    if (!/^[a-z][a-z0-9]*(?:_[a-z0-9]+)*$/.test(item.name)) {
      throw new Error(`${description}.name is not snake_case: ${item.name}`);
    }
    if (!/^[A-Z][A-Za-z0-9]*$/.test(item.leanModule)) {
      throw new Error(`${description}.leanModule is invalid: ${item.leanModule}`);
    }
    if (snakeToPascal(item.name) !== item.leanModule) {
      throw new Error(
        `${description}.leanModule must be ${snakeToPascal(item.name)} for ${item.name}`,
      );
    }
    if (item.specTarget !== `Project.${item.leanModule}.Spec`) {
      throw new Error(
        `${description}.specTarget must be Project.${item.leanModule}.Spec`,
      );
    }
    if (typeof item.complete !== "boolean") {
      throw new Error(`${description}.complete must be a boolean`);
    }
    if (names.has(item.name)) {
      throw new Error(`${registryPath}: duplicate case name ${item.name}`);
    }
    if (leanModules.has(item.leanModule)) {
      throw new Error(`${registryPath}: duplicate Lean module ${item.leanModule}`);
    }
    names.add(item.name);
    leanModules.add(item.leanModule);
  }
  return registry.cases;
}

function selectCase(cases, name) {
  const selected = cases.find((item) => item.name === name);
  if (!selected) {
    throw new Error(
      `unknown Talos case ${JSON.stringify(name)}; available cases: ${cases.map((item) => item.name).join(", ")}`,
    );
  }
  return selected;
}

function findExecutable(name) {
  for (const directory of (process.env.PATH || "").split(path.delimiter)) {
    if (!directory) continue;
    const candidate = path.join(directory, name);
    try {
      fs.accessSync(candidate, fs.constants.X_OK);
      return candidate;
    } catch (error) {
      if (error.code !== "ENOENT" && error.code !== "ENOTDIR" && error.code !== "EACCES") {
        throw error;
      }
    }
  }
  return null;
}

function findWasmTools() {
  if (process.env.WASM_TOOLS) {
    try {
      fs.accessSync(process.env.WASM_TOOLS, fs.constants.X_OK);
      return process.env.WASM_TOOLS;
    } catch (error) {
      throw new Error(
        `WASM_TOOLS is not executable: ${process.env.WASM_TOOLS}: ${error.message}`,
      );
    }
  }
  const fromPath = findExecutable("wasm-tools");
  if (fromPath) return fromPath;
  const fromCargo = path.join(os.homedir(), ".cargo", "bin", "wasm-tools");
  try {
    fs.accessSync(fromCargo, fs.constants.X_OK);
    return fromCargo;
  } catch (error) {
    if (error.code !== "ENOENT" && error.code !== "ENOTDIR" && error.code !== "EACCES") {
      throw error;
    }
    const expected = fs.readFileSync(path.join(repoRoot, ".wasm-tools-version"), "utf8").trim();
    throw new Error(`wasm-tools ${expected} was not found; install it or set WASM_TOOLS`);
  }
}

function checkPrerequisites() {
  const wasmTools = findWasmTools();
  run(
    "wasm-tools version check",
    path.join(repoRoot, "tools", "check-wasm-tools-version.sh"),
    [],
    { cwd: repoRoot, env: { ...process.env, WASM_TOOLS: wasmTools } },
  );
  try {
    fs.accessSync(verifier, fs.constants.X_OK);
    return wasmTools;
  } catch (error) {
    if (error.code !== "ENOENT" && error.code !== "ENOTDIR" && error.code !== "EACCES") {
      throw error;
    }
  }

  const verifierLakefile = path.join(verifierRoot, "lakefile.toml");
  if (!fs.existsSync(verifierLakefile)) {
    console.log("Fetching the pinned Talos dependency.");
    runLimited(
      "Talos dependency update",
      "15m",
      "lake",
      ["--no-ansi", "update"],
      proofRoot,
    );
  }
  if (!fs.existsSync(verifierLakefile)) {
    throw new Error(`Talos dependency does not contain ${verifierRoot}`);
  }
  console.log("Building the pinned Talos verifier.");
  runLimited(
    "Talos verifier build",
    "20m",
    "lake",
    ["--no-ansi", "build"],
    verifierRoot,
  );
  try {
    fs.accessSync(verifier, fs.constants.X_OK);
  } catch (error) {
    throw new Error(`Talos verifier build did not produce ${verifier}: ${error.message}`);
  }
  return wasmTools;
}

function buildCompilerInputs(cases) {
  const modules = [...new Set(cases.map((item) => item.module))];
  runLimited(
    "Lean source and compiler build",
    "10m",
    "lake",
    ["--no-ansi", "build", "lean-wasm", ...modules],
    repoRoot,
  );
  try {
    fs.accessSync(leanWasm, fs.constants.X_OK);
  } catch (error) {
    throw new Error(`compiler build did not produce ${leanWasm}: ${error.message}`);
  }
}

function replaceIfChanged(source, destination) {
  const content = fs.readFileSync(source);
  try {
    if (fs.readFileSync(destination).equals(content)) return false;
  } catch (error) {
    if (error.code !== "ENOENT") throw error;
  }
  fs.mkdirSync(path.dirname(destination), { recursive: true });
  const temporary = `${destination}.tmp-${process.pid}-${Date.now()}`;
  try {
    fs.writeFileSync(temporary, content);
    fs.renameSync(temporary, destination);
  } catch (error) {
    try {
      fs.rmSync(temporary, { force: true });
    } catch (cleanupError) {
      throw new AggregateError(
        [error, cleanupError],
        `could not replace ${destination} and could not remove ${temporary}`,
      );
    }
    throw error;
  }
  return true;
}

function prepareCase(item, wasmTools) {
  console.log(`Preparing Talos artifact: ${item.name}`);
  const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), "leanexe-talos-"));
  let operationError = null;
  try {
    const stageRoot = path.join(temporaryRoot, "stage");
    const wasm = path.join(stageRoot, "program.wasm");
    const wat = path.join(stageRoot, "program.wat");
    fs.mkdirSync(stageRoot, { recursive: true });

    runLimited(
      `${item.name} compiler run`,
      "10m",
      leanWasm,
      ["compile", "--module", item.module, "--entry", item.entry, "--out", wasm],
      repoRoot,
    );
    run(
      `${item.name} WAT rendering`,
      wasmTools,
      ["print", wasm, "-o", wat],
      { cwd: repoRoot },
    );

    const crateRoot = path.join(temporaryRoot, "rust", item.name);
    const buildRoot = path.join(temporaryRoot, "rust", "build", item.name);
    fs.mkdirSync(crateRoot, { recursive: true });
    fs.mkdirSync(buildRoot, { recursive: true });
    fs.writeFileSync(
      path.join(crateRoot, "Cargo.toml"),
      `[package]\nname = "${item.name}"\nversion = "0.0.0"\nedition = "2021"\n`,
    );
    fs.copyFileSync(wasm, path.join(buildRoot, "program.wasm"));
    fs.copyFileSync(wat, path.join(buildRoot, "program.wat"));

    runLimited(
      `${item.name} Talos model generation`,
      "10m",
      verifier,
      ["emit", "--force-emit", item.name],
      temporaryRoot,
    );
    const program = path.join(
      temporaryRoot,
      "lean",
      "Project",
      item.leanModule,
      "Program.lean",
    );
    if (!fs.existsSync(program)) {
      throw new Error(`${item.name}: Talos did not generate ${program}`);
    }

    const artifactRoot = path.join(generatedRoot, item.name);
    replaceIfChanged(wasm, path.join(artifactRoot, "program.wasm"));
    replaceIfChanged(wat, path.join(artifactRoot, "program.wat"));
    replaceIfChanged(
      program,
      path.join(proofRoot, "Project", item.leanModule, "Program.lean"),
    );
  } catch (error) {
    operationError = error;
  }

  try {
    fs.rmSync(temporaryRoot, { recursive: true });
  } catch (cleanupError) {
    if (operationError) {
      throw new AggregateError(
        [operationError, cleanupError],
        `${item.name}: generation and temporary-directory cleanup failed`,
      );
    }
    throw new Error(
      `${item.name}: could not remove temporary directory ${temporaryRoot}: ${cleanupError.message}`,
    );
  }
  if (operationError) throw operationError;
  console.log(`Prepared Talos artifact: ${item.name}`);
}

function prepareCases(cases) {
  const wasmTools = checkPrerequisites();
  buildCompilerInputs(cases);
  for (const item of cases) prepareCase(item, wasmTools);
}

function importedModules(file, suffix) {
  const source = fs.readFileSync(file, "utf8");
  const pattern = new RegExp(`^import Project\\.([A-Za-z0-9]+)\\.${suffix}$`, "gm");
  return new Set([...source.matchAll(pattern)].map((match) => match[1]));
}

function assertEqualSets(description, expected, actual) {
  const missing = [...expected].filter((item) => !actual.has(item)).sort();
  const extra = [...actual].filter((item) => !expected.has(item)).sort();
  if (missing.length === 0 && extra.length === 0) return;
  const details = [];
  if (missing.length > 0) details.push(`missing: ${missing.join(", ")}`);
  if (extra.length > 0) details.push(`unexpected: ${extra.join(", ")}`);
  throw new Error(`${description} does not match cases.json (${details.join("; ")})`);
}

function checkAggregateImports(cases) {
  const completed = new Set(
    cases.filter((item) => item.complete).map((item) => item.leanModule),
  );
  const specs = importedModules(path.join(proofRoot, "Project.lean"), "Spec");
  specs.delete("Runtime");
  assertEqualSets("Project.lean specification imports", completed, specs);

  const programs = importedModules(
    path.join(proofRoot, "Project", "Runtime", "Checks.lean"),
    "Program",
  );
  assertEqualSets(
    "Project.Runtime.Checks program imports",
    new Set(cases.map((item) => item.leanModule)),
    programs,
  );
}

function checkCase(item) {
  runLimited(
    `${item.name} proof build`,
    "15m",
    "lake",
    ["--no-ansi", "build", item.specTarget],
    proofRoot,
  );
}

function checkAllProofs(cases) {
  checkAggregateImports(cases);
  runLimited(
    "aggregate Talos proof build",
    "20m",
    "lake",
    ["--no-ansi", "build", "Project"],
    proofRoot,
  );
}

function formatError(error) {
  if (error instanceof AggregateError) {
    return [error.message, ...error.errors.map((item) => formatError(item))].join("\n");
  }
  return error instanceof Error ? error.message : String(error);
}

module.exports = {
  checkAggregateImports,
  checkAllProofs,
  checkCase,
  formatError,
  loadRegistry,
  prepareCases,
  selectCase,
};
