#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const workDir = path.join(".lake", "build", "standard-compare");
const defaultMaxInputBytes = 4096;
const defaultMaxArgs = 8;
const defaultMaxArgBytes = 4096;
const validModes = new Set([
  "wasi",
  "stdin",
  "stdin-except",
  "argv-except",
  "stdin-argv-except",
]);
const builtTargets = new Set();

function usage() {
  process.stdout.write(`Usage:
  node tools/compare-standard.js --mode MODE --module MODULE --entry ENTRY [options] [-- args...]
  node tools/compare-standard.js --self-test

Modes:
  wasi               ByteArray
  stdin              ByteArray -> ByteArray
  stdin-except       ByteArray -> Except ByteArray ByteArray
  argv-except        Array ByteArray -> Except ByteArray ByteArray
  stdin-argv-except  ByteArray -> Array ByteArray -> Except ByteArray ByteArray

Options:
  --stdin TEXT
  --stdin-file PATH
  --arg VALUE
  --max-input-bytes N
  --max-args N
  --max-argv-bytes N
  --keep
`);
}

function run(args, options = {}) {
  const result = spawnSync(args[0], args.slice(1), options);
  if (result.status === null && result.error) {
    throw result.error;
  }
  return result;
}

function outputText(result) {
  return Buffer.concat([result.stdout || Buffer.alloc(0), result.stderr || Buffer.alloc(0)]).toString("utf8");
}

function requireSuccess(result, command) {
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${command} failed`);
  }
}

function buildTarget(target) {
  if (builtTargets.has(target)) {
    return;
  }
  requireSuccess(run(["lake", "build", target], { encoding: null }), `lake build ${target}`);
  builtTargets.add(target);
}

function ensureBuilt(moduleName) {
  buildTarget("lean-wasm");
  buildTarget(moduleName);
}

function ensureWorkDir() {
  fs.mkdirSync(workDir, { recursive: true });
}

function leanString(text) {
  return `"${text.replace(/\\/g, "\\\\").replace(/"/g, "\\\"")}"`;
}

function safeName(text) {
  return text.replace(/[^A-Za-z0-9_.-]/g, "_");
}

function entryInfo(moduleName, entry) {
  if (entry.includes(".")) {
    return {
      fullEntry: entry,
      shortEntry: entry.slice(entry.lastIndexOf(".") + 1),
    };
  }
  return {
    fullEntry: `${moduleName}.${entry}`,
    shortEntry: entry,
  };
}

function parsePositiveInteger(name, value) {
  const parsed = Number(value);
  if (!Number.isInteger(parsed) || parsed <= 0) {
    throw new Error(`${name} must be a positive integer`);
  }
  return parsed;
}

function parseArgs(argv) {
  const config = {
    mode: "",
    moduleName: "",
    entry: "",
    input: Buffer.alloc(0),
    programArgs: [],
    maxInputBytes: defaultMaxInputBytes,
    maxArgs: defaultMaxArgs,
    maxArgBytes: defaultMaxArgBytes,
    keep: false,
    selfTest: false,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--") {
      config.programArgs.push(...argv.slice(i + 1));
      break;
    } else if (arg === "--help" || arg === "-h") {
      usage();
      process.exit(0);
    } else if (arg === "--self-test") {
      config.selfTest = true;
    } else if (arg === "--mode") {
      config.mode = argv[++i] || "";
    } else if (arg === "--module") {
      config.moduleName = argv[++i] || "";
    } else if (arg === "--entry") {
      config.entry = argv[++i] || "";
    } else if (arg === "--stdin") {
      config.input = Buffer.from(argv[++i] || "", "utf8");
    } else if (arg === "--stdin-file") {
      const inputPath = argv[++i] || "";
      config.input = fs.readFileSync(inputPath);
    } else if (arg === "--arg") {
      config.programArgs.push(argv[++i] || "");
    } else if (arg === "--max-input-bytes") {
      config.maxInputBytes = parsePositiveInteger("--max-input-bytes", argv[++i] || "");
    } else if (arg === "--max-args") {
      config.maxArgs = parsePositiveInteger("--max-args", argv[++i] || "");
    } else if (arg === "--max-argv-bytes") {
      config.maxArgBytes = parsePositiveInteger("--max-argv-bytes", argv[++i] || "");
    } else if (arg === "--keep") {
      config.keep = true;
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }

  return config;
}

function validateConfig(config) {
  if (!validModes.has(config.mode)) {
    throw new Error(`unsupported mode: ${config.mode || "(missing)"}`);
  }
  if (!config.moduleName) {
    throw new Error("--module is required");
  }
  if (!config.entry) {
    throw new Error("--entry is required");
  }
  if (config.input.length > config.maxInputBytes) {
    throw new Error(`stdin has ${config.input.length} bytes, but --max-input-bytes is ${config.maxInputBytes}`);
  }
  if (config.programArgs.length > config.maxArgs) {
    throw new Error(`${config.programArgs.length} arguments exceed --max-args ${config.maxArgs}`);
  }
}

function validateArgvBytes(config, paths) {
  if (config.mode !== "argv-except" && config.mode !== "stdin-argv-except") {
    return;
  }
  const argv0Bytes = Buffer.byteLength(paths.wasm, "utf8") + 1;
  const userArgBytes = config.programArgs.reduce((sum, value) => sum + Buffer.byteLength(value, "utf8") + 1, 0);
  const argvBytes = argv0Bytes + userArgBytes;
  if (argvBytes > config.maxArgBytes) {
    throw new Error(`${argvBytes} WASI argv bytes exceed --max-argv-bytes ${config.maxArgBytes}`);
  }
}

function runnerSource(config, paths, fullEntry) {
  const header = [
    `import ${config.moduleName}`,
    "",
    `def __leanexeInputPath : System.FilePath := System.FilePath.mk ${leanString(paths.input)}`,
    `def __leanexeStdoutPath : System.FilePath := System.FilePath.mk ${leanString(paths.standardStdout)}`,
    `def __leanexeStderrPath : System.FilePath := System.FilePath.mk ${leanString(paths.standardStderr)}`,
    "",
    "def __leanexeOk (bytes : ByteArray) : IO UInt32 := do",
    "  IO.FS.writeBinFile __leanexeStdoutPath bytes",
    "  IO.FS.writeBinFile __leanexeStderrPath ByteArray.empty",
    "  return 0",
    "",
    "def __leanexeErr (bytes : ByteArray) : IO UInt32 := do",
    "  IO.FS.writeBinFile __leanexeStdoutPath ByteArray.empty",
    "  IO.FS.writeBinFile __leanexeStderrPath bytes",
    "  return 1",
    "",
  ];

  if (config.mode === "wasi") {
    return `${header.join("\n")}def main (_args : List String) : IO UInt32 := do
  __leanexeOk ${fullEntry}
`;
  }
  if (config.mode === "stdin") {
    return `${header.join("\n")}def main (_args : List String) : IO UInt32 := do
  let input <- IO.FS.readBinFile __leanexeInputPath
  __leanexeOk (${fullEntry} input)
`;
  }
  if (config.mode === "stdin-except") {
    return `${header.join("\n")}def main (_args : List String) : IO UInt32 := do
  let input <- IO.FS.readBinFile __leanexeInputPath
  match ${fullEntry} input with
  | Except.ok bytes => __leanexeOk bytes
  | Except.error bytes => __leanexeErr bytes
`;
  }
  if (config.mode === "argv-except") {
    return `${header.join("\n")}def main (args : List String) : IO UInt32 := do
  let programArgs : Array ByteArray := args.toArray.map (fun arg => arg.toUTF8)
  match ${fullEntry} programArgs with
  | Except.ok bytes => __leanexeOk bytes
  | Except.error bytes => __leanexeErr bytes
`;
  }
  if (config.mode === "stdin-argv-except") {
    return `${header.join("\n")}def main (args : List String) : IO UInt32 := do
  let input <- IO.FS.readBinFile __leanexeInputPath
  let programArgs : Array ByteArray := args.toArray.map (fun arg => arg.toUTF8)
  match ${fullEntry} input programArgs with
  | Except.ok bytes => __leanexeOk bytes
  | Except.error bytes => __leanexeErr bytes
`;
  }
  throw new Error(`unsupported mode: ${config.mode}`);
}

function pathsFor(config, fullEntry, shortEntry) {
  const base = safeName(`${config.mode}.${fullEntry}`);
  return {
    runner: path.join(workDir, `${base}.runner.lean`),
    input: path.join(workDir, `${base}.stdin`),
    standardStdout: path.join(workDir, `${base}.standard.stdout`),
    standardStderr: path.join(workDir, `${base}.standard.stderr`),
    wasm: path.join(workDir, `${safeName(config.mode)}.${safeName(shortEntry)}.wasm`),
  };
}

function compileWasm(config, paths, fullEntry) {
  const args = [leanExe];
  if (config.mode === "wasi") {
    args.push("compile-wasi");
  } else if (config.mode === "stdin") {
    args.push("compile-wasi-stdin", "--max-input-bytes", config.maxInputBytes.toString());
  } else if (config.mode === "stdin-except") {
    args.push("compile-wasi-stdin-except", "--max-input-bytes", config.maxInputBytes.toString());
  } else if (config.mode === "argv-except") {
    args.push(
      "compile-wasi-argv-except",
      "--max-args",
      config.maxArgs.toString(),
      "--max-argv-bytes",
      config.maxArgBytes.toString(),
    );
  } else if (config.mode === "stdin-argv-except") {
    args.push(
      "compile-wasi-stdin-argv-except",
      "--max-input-bytes",
      config.maxInputBytes.toString(),
      "--max-args",
      config.maxArgs.toString(),
      "--max-argv-bytes",
      config.maxArgBytes.toString(),
    );
  } else {
    throw new Error(`unsupported mode: ${config.mode}`);
  }
  args.push("--module", config.moduleName, "--entry", fullEntry, "--out", paths.wasm);
  requireSuccess(run(args, { encoding: null }), `${leanExe} ${args.slice(1).join(" ")}`);
}

function runStandard(config, paths, fullEntry) {
  fs.writeFileSync(paths.input, config.input);
  fs.writeFileSync(paths.standardStdout, Buffer.alloc(0));
  fs.writeFileSync(paths.standardStderr, Buffer.alloc(0));
  fs.writeFileSync(paths.runner, runnerSource(config, paths, fullEntry));

  const result = run(["lake", "env", "lean", "--run", paths.runner, ...config.programArgs], {
    encoding: null,
    timeout: 10000,
  });
  const stdout = fs.readFileSync(paths.standardStdout);
  const stderr = fs.readFileSync(paths.standardStderr);
  const processOutput = outputText(result).trim();
  if (processOutput.length !== 0) {
    throw new Error(`standard Lean runner produced process output:\n${processOutput}`);
  }
  return { status: result.status, stdout, stderr };
}

function runWasm(config, paths) {
  const usesStdin =
    config.mode === "stdin" ||
    config.mode === "stdin-except" ||
    config.mode === "stdin-argv-except";
  const stdinFd = usesStdin ? fs.openSync(paths.input, "r") : null;
  try {
    const result = run([wasmtime, "run", paths.wasm, ...config.programArgs], {
      encoding: null,
      stdio: [stdinFd === null ? "ignore" : stdinFd, "pipe", "pipe"],
      timeout: 10000,
    });
    return {
      status: result.status,
      stdout: result.stdout || Buffer.alloc(0),
      stderr: result.stderr || Buffer.alloc(0),
    };
  } finally {
    if (stdinFd !== null) {
      fs.closeSync(stdinFd);
    }
  }
}

function describeBytes(bytes) {
  const text = bytes.toString("utf8");
  if (/^[\x09\x0a\x0d\x20-\x7e]*$/.test(text)) {
    return JSON.stringify(text);
  }
  return `0x${bytes.toString("hex")}`;
}

function compareResults(config, standard, wasm) {
  const problems = [];
  if (standard.status !== wasm.status) {
    problems.push(`status: standard ${standard.status}, wasm ${wasm.status}`);
  }
  if (Buffer.compare(standard.stdout, wasm.stdout) !== 0) {
    problems.push(`stdout: standard ${describeBytes(standard.stdout)}, wasm ${describeBytes(wasm.stdout)}`);
  }
  if (Buffer.compare(standard.stderr, wasm.stderr) !== 0) {
    problems.push(`stderr: standard ${describeBytes(standard.stderr)}, wasm ${describeBytes(wasm.stderr)}`);
  }
  if (problems.length !== 0) {
    throw new Error(`${config.moduleName}.${config.entry} differs:\n${problems.join("\n")}`);
  }
}

function compareCase(inputConfig) {
  const config = {
    maxInputBytes: defaultMaxInputBytes,
    maxArgs: defaultMaxArgs,
    maxArgBytes: defaultMaxArgBytes,
    input: Buffer.alloc(0),
    programArgs: [],
    keep: false,
    ...inputConfig,
  };
  validateConfig(config);
  const { fullEntry, shortEntry } = entryInfo(config.moduleName, config.entry);
  const paths = pathsFor(config, fullEntry, shortEntry);
  validateArgvBytes(config, paths);

  ensureWorkDir();
  ensureBuilt(config.moduleName);
  compileWasm(config, paths, fullEntry);
  const standard = runStandard(config, paths, fullEntry);
  const wasm = runWasm(config, paths);
  compareResults(config, standard, wasm);

  if (!config.keep) {
    for (const file of [paths.runner, paths.input, paths.standardStdout, paths.standardStderr, paths.wasm]) {
      fs.rmSync(file, { force: true });
    }
  }
  process.stdout.write(`matched ${config.mode} ${fullEntry}\n`);
}

function selfTest() {
  const cases = [
    {
      mode: "wasi",
      moduleName: "LeanExe.Examples.Correctness",
      entry: "byteArrayStringConstReturn",
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.ByteArrayPrograms",
      entry: "appendBang",
      input: Buffer.from("AB", "utf8"),
      maxInputBytes: 8,
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonGcd",
      entry: "transform",
      input: Buffer.from("[48,18,30]", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonGcd",
      entry: "transform",
      input: Buffer.from("[]", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonTreeCommand",
      entry: "makeTree",
      input: Buffer.from("[1,6,4,100,33,5,5,20]", "utf8"),
      maxInputBytes: 4096,
    },
    {
      mode: "argv-except",
      moduleName: "LeanExe.Examples.ByteArrayPrograms",
      entry: "argvFirstLast",
      programArgs: ["alpha", "omega"],
    },
  ];
  for (const testCase of cases) {
    compareCase(testCase);
  }
  process.stdout.write(`checked ${cases.length} standard Lean comparison cases\n`);
}

try {
  const config = parseArgs(process.argv.slice(2));
  if (config.selfTest) {
    selfTest();
  } else {
    validateConfig(config);
    compareCase({
      mode: config.mode,
      moduleName: config.moduleName,
      entry: config.entry,
      input: config.input,
      programArgs: config.programArgs,
      maxInputBytes: config.maxInputBytes,
      maxArgs: config.maxArgs,
      maxArgBytes: config.maxArgBytes,
      keep: config.keep,
    });
  }
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
