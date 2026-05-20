#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const crypto = require("crypto");
const { spawnSync } = require("child_process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const workDir = path.join(".lake", "build", "standard-compare");
const defaultMaxInputBytes = 4096;
const defaultMaxArgs = 8;
const defaultMaxArgBytes = 4096;
const validModes = new Set([
  "pure",
  "pure-bytes",
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
  pure               Library export invoked with wasmtime --invoke
  pure-bytes         Concrete pure call serialized to ByteArray and run as WASI
  wasi               ByteArray
  stdin              ByteArray -> ByteArray
  stdin-except       ByteArray -> Except ByteArray ByteArray
  argv-except        Array ByteArray -> Except ByteArray ByteArray
  stdin-argv-except  ByteArray -> Array ByteArray -> Except ByteArray ByteArray

Options:
  --standard-call LEAN_EXPR
  --result-slots LEAN_EXPR
  --serializer LEAN_EXPR
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
    standardCall: "",
    resultSlots: "",
    serializer: "",
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
    } else if (arg === "--standard-call") {
      config.standardCall = argv[++i] || "";
    } else if (arg === "--result-slots") {
      config.resultSlots = argv[++i] || "";
    } else if (arg === "--serializer") {
      config.serializer = argv[++i] || "";
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
  if (config.mode === "pure" && !config.resultSlots) {
    throw new Error("--result-slots is required for pure mode");
  }
  if (config.mode === "pure-bytes" && !config.serializer) {
    throw new Error("--serializer is required for pure-bytes mode");
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

function pureStandardCall(config, fullEntry) {
  if (config.standardCall) {
    return config.standardCall;
  }
  const args = config.programArgs.join(" ");
  if (args.length === 0) {
    return fullEntry;
  }
  return `(${fullEntry} ${args})`;
}

function pureRunnerSource(config, fullEntry) {
  return `import ${config.moduleName}

def __leanexeWriteSlots (values : Array UInt64) : IO UInt32 := do
  for value in values do
    IO.println value
  return 0

def main (_args : List String) : IO UInt32 := do
  let __leanexeValue := ${pureStandardCall(config, fullEntry)}
  __leanexeWriteSlots (${config.resultSlots})
`;
}

function serializedSupportDefs() {
  return `def __leanexeAppendUInt64 (out : ByteArray) (value : UInt64) : ByteArray :=
  LeanExe.Ascii.appendUInt64Decimal out value

def __leanexeAppendNat (out : ByteArray) (value : Nat) : ByteArray :=
  LeanExe.Ascii.appendUInt64Decimal out (UInt64.ofNat value)

def __leanexeSep (out : ByteArray) : ByteArray :=
  out.push (10 : UInt8)
`;
}

function pureBytesRunnerSource(config, paths, fullEntry) {
  return `import ${config.moduleName}
import LeanExe.Ascii.Decimal

${serializedSupportDefs()}

def __leanexeInputPath : System.FilePath := System.FilePath.mk ${leanString(paths.input)}
def __leanexeStdoutPath : System.FilePath := System.FilePath.mk ${leanString(paths.standardStdout)}
def __leanexeStderrPath : System.FilePath := System.FilePath.mk ${leanString(paths.standardStderr)}

def __leanexeOk (bytes : ByteArray) : IO UInt32 := do
  IO.FS.writeBinFile __leanexeStdoutPath bytes
  IO.FS.writeBinFile __leanexeStderrPath ByteArray.empty
  return 0

def main (_args : List String) : IO UInt32 := do
  let __leanexeValue := ${pureStandardCall(config, fullEntry)}
  __leanexeOk (${config.serializer})
`;
}

function pureBytesWrapperSource(config, paths, fullEntry) {
  return `import ${config.moduleName}
import LeanExe.Ascii.Decimal

namespace ${paths.wrapperModule}

${serializedSupportDefs()}

def __leanexeEntry : ByteArray :=
  let __leanexeValue := ${pureStandardCall(config, fullEntry)}
  ${config.serializer}

end ${paths.wrapperModule}
`;
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
  const wrapperHash = crypto.createHash("sha1")
    .update(JSON.stringify({
      mode: config.mode,
      moduleName: config.moduleName,
      entry: fullEntry,
      args: config.programArgs,
      standardCall: config.standardCall,
      serializer: config.serializer,
    }))
    .digest("hex")
    .slice(0, 16);
  const wrapperName = `Case_${wrapperHash}`;
  const wrapperModule = `LeanExe.StandardCompare.${wrapperName}`;
  return {
    runner: path.join(workDir, `${base}.runner.lean`),
    input: path.join(workDir, `${base}.stdin`),
    standardStdout: path.join(workDir, `${base}.standard.stdout`),
    standardStderr: path.join(workDir, `${base}.standard.stderr`),
    wasm: path.join(workDir, `${safeName(config.mode)}.${safeName(shortEntry)}.wasm`),
    wrapperModule,
    wrapperSource: path.join("LeanExe", "StandardCompare", `${wrapperName}.lean`),
    wrapperOlean: path.join(".lake", "build", "lib", "lean", "LeanExe", "StandardCompare", `${wrapperName}.olean`),
  };
}

function buildPureBytesWrapper(config, paths, fullEntry) {
  fs.mkdirSync(path.dirname(paths.wrapperSource), { recursive: true });
  fs.mkdirSync(path.dirname(paths.wrapperOlean), { recursive: true });
  fs.writeFileSync(paths.wrapperSource, pureBytesWrapperSource(config, paths, fullEntry));
  requireSuccess(
    run(["lake", "env", "lean", "-o", paths.wrapperOlean, paths.wrapperSource], { encoding: null }),
    `lake env lean -o ${paths.wrapperOlean} ${paths.wrapperSource}`,
  );
}

function compileWasm(config, paths, fullEntry) {
  const args = [leanExe];
  if (config.mode === "pure") {
    args.push("compile");
  } else if (config.mode === "pure-bytes") {
    buildPureBytesWrapper(config, paths, fullEntry);
    args.push("compile-wasi");
  } else if (config.mode === "wasi") {
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
  if (config.mode === "pure-bytes") {
    args.push("--module", paths.wrapperModule, "--entry", `${paths.wrapperModule}.__leanexeEntry`);
  } else {
    args.push("--module", config.moduleName, "--entry", fullEntry);
  }
  args.push("--out", paths.wasm);
  requireSuccess(run(args, { encoding: null }), `${leanExe} ${args.slice(1).join(" ")}`);
}

function runStandard(config, paths, fullEntry) {
  fs.writeFileSync(paths.input, config.input);
  fs.writeFileSync(paths.standardStdout, Buffer.alloc(0));
  fs.writeFileSync(paths.standardStderr, Buffer.alloc(0));
  fs.writeFileSync(paths.runner,
    config.mode === "pure"
      ? pureRunnerSource(config, fullEntry)
      : config.mode === "pure-bytes"
        ? pureBytesRunnerSource(config, paths, fullEntry)
        : runnerSource(config, paths, fullEntry));

  const result = run(["lake", "env", "lean", "--run", paths.runner, ...config.programArgs], {
    encoding: null,
    timeout: 10000,
  });
  if (config.mode === "pure") {
    return {
      status: result.status,
      stdout: result.stdout || Buffer.alloc(0),
      stderr: result.stderr || Buffer.alloc(0),
    };
  }
  const stdout = fs.readFileSync(paths.standardStdout);
  const stderr = fs.readFileSync(paths.standardStderr);
  const processOutput = outputText(result).trim();
  if (processOutput.length !== 0) {
    throw new Error(`standard Lean runner produced process output:\n${processOutput}`);
  }
  return { status: result.status, stdout, stderr };
}

function runWasm(config, paths, shortEntry) {
  if (config.mode === "pure") {
    const result = run([wasmtime, "--invoke", shortEntry, paths.wasm, ...config.programArgs], {
      encoding: null,
      timeout: 10000,
    });
    return {
      status: result.status,
      stdout: result.stdout || Buffer.alloc(0),
      stderr: result.status === 0 ? Buffer.alloc(0) : result.stderr || Buffer.alloc(0),
    };
  }
  if (config.mode === "pure-bytes") {
    const result = run([wasmtime, "run", paths.wasm], {
      encoding: null,
      stdio: ["ignore", "pipe", "pipe"],
      timeout: 10000,
    });
    return {
      status: result.status,
      stdout: result.stdout || Buffer.alloc(0),
      stderr: result.stderr || Buffer.alloc(0),
    };
  }
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
  const wasm = runWasm(config, paths, shortEntry);
  compareResults(config, standard, wasm);

  if (!config.keep) {
    for (const file of [
      paths.runner,
      paths.input,
      paths.standardStdout,
      paths.standardStderr,
      paths.wasm,
      paths.wrapperSource,
      paths.wrapperOlean,
    ]) {
      fs.rmSync(file, { force: true });
    }
  }
  process.stdout.write(`matched ${config.mode} ${fullEntry}\n`);
}

function selfTest() {
  const correctness = "LeanExe.Examples.Correctness";
  const cases = [
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idFunctionUInt64",
      programArgs: ["4"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunNestedArrayForSum",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunWhileBreakContinue",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutNestedIf",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutStructureReturn",
      resultSlots: "#[__leanexeValue.x, __leanexeValue.y]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutOptionReturn",
      resultSlots:
        "match __leanexeValue with | none => #[0, 0] | some value => #[1, value]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutExceptReturn",
      resultSlots:
        "match __leanexeValue with | Except.error code => #[0, code, 0] | Except.ok value => #[1, 0, value]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutOptionMatch",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutOptionIfLet",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutOptionCatchAllMatch",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutStatusMatchReturn",
      resultSlots:
        "match __leanexeValue with | .ok value => #[0, value, 0] | .error code => #[1, 0, code]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutStatusIfLet",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutStatusCatchAllMatch",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutModeIfLet",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunWhileStatusIfLetSum",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunMutMatchStateRecord",
      resultSlots: "#[UInt64.ofNat __leanexeValue.pos, __leanexeValue.sum]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunWhileDigitScanner",
      resultSlots: "#[UInt64.ofNat __leanexeValue.pos, __leanexeValue.sum]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunWhileParserExcept",
      resultSlots:
        "match __leanexeValue with | Except.error code => #[0, code, 0, 0] | Except.ok state => #[1, 0, UInt64.ofNat state.pos, state.sum]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "idRunWhileArrayUpdateSum",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptDoStateFromLoop",
      resultSlots:
        "match __leanexeValue with | Except.error code => #[0, code, 0, 0] | Except.ok state => #[1, 0, UInt64.ofNat state.pos, state.sum]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptDoLoopErrorSkipsRestTrap",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptDoStatusFromLoop",
      resultSlots:
        "match __leanexeValue with | Except.error code => #[0, code, 0, 0, 0] | Except.ok status => match status with | .ok value => #[1, 0, 0, value, 0] | .error code => #[1, 0, 1, 0, code]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natDivModNormal",
      programArgs: ["7"],
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "structureReturn",
      programArgs: ["4"],
      resultSlots: "#[__leanexeValue.x, __leanexeValue.y]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "structureParam",
      programArgs: ["2", "3"],
      standardCall:
        `${correctness}.structureParam ({ x := (2 : UInt64), y := (3 : UInt64) } : ${correctness}.Point)`,
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "genericInterleavedLambdaHelper",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "statusBranchReturn",
      programArgs: ["0"],
      resultSlots:
        "match __leanexeValue with | .ok value => #[0, value, 0] | .error code => #[1, 0, code]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "statusParam",
      programArgs: ["0", "5", "0"],
      standardCall: `${correctness}.statusParam (${correctness}.Status.ok 5)`,
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "productEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "structurePropEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "inductiveEqualityDifferentCtor",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionStructuralEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "byteArrayEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "pointArrayEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "nestedArrayEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "byteArrayStructureArrayEquality",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayReturnABC",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayBranchHelperReturn",
      programArgs: ["1"],
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayResultDropsOwnedTemp",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "idRunWhileByteArrayOutput",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "idRunMutByteArrayReturn",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "idRunWhileDigitOutput",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptDoByteArrayFromValidation",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok bytes => bytes`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "idRunWhileParserBufferState",
      serializer: `let out := __leanexeAppendNat ByteArray.empty __leanexeValue.pos
let out := __leanexeSep out
let out := out ++ __leanexeValue.out
let out := __leanexeSep out
__leanexeAppendUInt64 out (if __leanexeValue.ok then 1 else 0)`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "idRunWhileArrayBuilderState",
      serializer: `let out := __leanexeAppendNat ByteArray.empty __leanexeValue.values.size
let out := __leanexeValue.values.foldl (fun out value =>
  let out := __leanexeSep out
  __leanexeAppendUInt64 out value) out
let out := __leanexeSep out
__leanexeAppendUInt64 out __leanexeValue.count`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "structureArrayReturn",
      serializer: `let out := __leanexeAppendNat ByteArray.empty __leanexeValue.values.size
let out := __leanexeValue.values.foldl (fun out value =>
  let out := __leanexeSep out
  __leanexeAppendUInt64 out value) out
let out := __leanexeSep out
__leanexeAppendUInt64 out __leanexeValue.count`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "structurePointArrayReturn",
      serializer: `let out := __leanexeAppendNat ByteArray.empty __leanexeValue.values.size
let out := __leanexeValue.values.foldl (fun out point =>
  let out := __leanexeSep out
  let out := __leanexeAppendUInt64 out point.x
  let out := __leanexeSep out
  __leanexeAppendUInt64 out point.y) out
let out := __leanexeSep out
__leanexeAppendUInt64 out __leanexeValue.count`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayFoldByteOutputState",
      serializer: `let out := __leanexeAppendUInt64 ByteArray.empty __leanexeValue.count
let out := __leanexeSep out
out ++ __leanexeValue.bytes`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "arrayFoldByteOutputState",
      serializer: `let out := __leanexeAppendUInt64 ByteArray.empty __leanexeValue.count
let out := __leanexeSep out
out ++ __leanexeValue.bytes`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "arrayFoldMExceptErrorSkipsRestTrap",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok value => __leanexeAppendUInt64 "ok".toUTF8 value`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "arrayFoldMOptionSuccess",
      serializer: `match __leanexeValue with
| some value => __leanexeAppendUInt64 ByteArray.empty value
| none => "none".toUTF8`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "arrayAttachFoldMExcept",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok value => __leanexeAppendUInt64 "ok".toUTF8 value`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayFoldMExceptErrorSkipsRestTrap",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok value => __leanexeAppendUInt64 "ok".toUTF8 value`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayFoldMOptionByteArray",
      serializer: `match __leanexeValue with
| some bytes => bytes
| none => "none".toUTF8`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64ListTailValue",
      serializer: `${correctness}.u64ListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListAppendRecValue",
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListReverseValue",
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListMapValue",
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListFilterValue",
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListBoxValue",
      serializer: `${correctness}.leanListBoxBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64TreeValue",
      serializer: `${correctness}.u64TreeBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryValue",
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "recursiveResultDropsOwnedTemp",
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryMapValue",
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryMirrorValue",
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryInsertValue",
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryFindValue",
      serializer: `${correctness}.u64BinaryOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryFindMissingValue",
      serializer: `${correctness}.u64BinaryOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryRequireValue",
      serializer: `${correctness}.u64BinaryExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryRequireMissingValue",
      serializer: `${correctness}.u64BinaryExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryBoxValue",
      serializer: `${correctness}.u64BinaryBoxBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "mutJsonValue",
      serializer: `${correctness}.mutJsonBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: "LeanExe.Ascii.Json.Value",
      entry: "LeanExe.Ascii.Json.parseBytes",
      standardCall: `LeanExe.Ascii.Json.parseBytes "{\\"a\\":[1,true,null],\\"b\\":{\\"c\\":\\"ok\\"}}".toUTF8`,
      serializer: `match __leanexeValue with
| some value => LeanExe.Ascii.Json.render value
| none => "none".toUTF8`,
    },
    {
      mode: "wasi",
      moduleName: correctness,
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
      moduleName: "LeanExe.Examples.JsonTypedDecode",
      entry: "transform",
      input: Buffer.from("{\"values\":[6,10,14],\"multiplier\":2,\"includeCount\":true}", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonObjectArrayDecode",
      entry: "transform",
      input: Buffer.from("{\"items\":[{\"id\":1,\"weight\":4},{\"id\":2,\"weight\":7}],\"scale\":3}", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonAdd",
      entry: "transform",
      input: Buffer.from("{\"a\":19,\"b\":23}", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonCollatzLength",
      entry: "transform",
      input: Buffer.from("{\"collatzLengthFor\":41}", "utf8"),
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
      standardCall: config.standardCall,
      resultSlots: config.resultSlots,
      serializer: config.serializer,
      keep: config.keep,
    });
  }
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
