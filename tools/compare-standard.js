#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const crypto = require("crypto");
const { spawnResult } = require("./run-process");
const host = require("../test/wasmtime_host");
const {
  HostPlan,
  arrayLayout,
  assertAbiEqual,
  byteArrayLayout,
  decodePublicValue,
  layoutFromDescriptor,
  materializeArgPlan,
  resultReadCommands,
  scalarLayout,
  structLayout,
  variantLayout,
} = require("./abi_layout");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const workDir = path.join(".lake", "build", "standard-compare");
const defaultMaxInputBytes = 4096;
const defaultMaxArgs = 8;
const defaultMaxArgBytes = 4096;
const validModes = new Set([
  "pure",
  "pure-abi",
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
  pure-abi           Library export invoked through Wasmtime C host and decoded by ABI layout
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
  --abi-layout JSON
  --abi-arg JSON
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
  return spawnResult(args, options);
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
    resultLayout: null,
    abiArgs: null,
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
    } else if (arg === "--abi-layout") {
      config.resultLayout = JSON.parse(argv[++i] || "null");
    } else if (arg === "--abi-arg") {
      if (config.abiArgs === null) {
        config.abiArgs = [];
      }
      config.abiArgs.push(JSON.parse(argv[++i] || "null"));
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
  if (config.mode === "pure-abi" && !config.serializer) {
    throw new Error("--serializer is required for pure-abi mode");
  }
  if (config.mode === "pure-abi" && !config.resultLayout) {
    throw new Error("--abi-layout is required for pure-abi mode");
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

def __leanexeJsonUInt64 (value : UInt64) : ByteArray :=
  __leanexeAppendUInt64 ByteArray.empty value

def __leanexeJsonNat (value : Nat) : ByteArray :=
  __leanexeAppendNat ByteArray.empty value

def __leanexeJsonArray {α : Type} (items : Array α) (render : α -> ByteArray) : ByteArray :=
  let state :=
    items.foldl
      (fun state item =>
        let out := if state.1 then state.2 else state.2.push (44 : UInt8)
        (false, out ++ render item))
      (true, ByteArray.empty.push (91 : UInt8))
  state.2.push (93 : UInt8)

def __leanexeJsonByteArray (bytes : ByteArray) : ByteArray :=
  let state :=
    bytes.foldl
      (fun state byte =>
        let out := if state.1 then state.2 else state.2.push (44 : UInt8)
        (false, __leanexeAppendUInt64 out byte.toUInt64))
      (true, ByteArray.empty.push (91 : UInt8))
  state.2.push (93 : UInt8)
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

function normalizePureWasmStdout(bytes) {
  const text = bytes.toString("utf8");
  if (text.length === 0 || !/^-?\d+(\n-?\d+)*\n?$/.test(text)) {
    return bytes;
  }
  const trailingNewline = text.endsWith("\n");
  const lines = text.trimEnd().split("\n").map((line) =>
    BigInt.asUintN(64, BigInt(line)).toString());
  return Buffer.from(lines.join("\n") + (trailingNewline ? "\n" : ""), "utf8");
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
      abiArgs: config.abiArgs,
      resultLayout: config.resultLayout,
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
  if (config.mode === "pure" || config.mode === "pure-abi") {
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
      : config.mode === "pure-bytes" || config.mode === "pure-abi"
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
      stdout: result.status === 0
        ? normalizePureWasmStdout(result.stdout || Buffer.alloc(0))
        : result.stdout || Buffer.alloc(0),
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

function resolveLayout(layout) {
  if (layout && typeof layout.publicSlots === "number") {
    return layout;
  }
  return layoutFromDescriptor(layout);
}

function resolveAbiArg(arg) {
  if (arg && typeof arg === "object" && arg.layout) {
    return {
      layout: resolveLayout(arg.layout),
      value: arg.value,
    };
  }
  return arg;
}

function wasmAbiArgs(config) {
  if (config.abiArgs !== null) {
    return config.abiArgs.map(resolveAbiArg);
  }
  return config.programArgs;
}

function parseStandardAbiValue(config, standard, layout) {
  if (standard.status !== 0) {
    throw new Error(`${config.moduleName}.${config.entry} standard Lean runner failed with status ${standard.status}`);
  }
  if (standard.stderr.length !== 0) {
    throw new Error(`${config.moduleName}.${config.entry} standard Lean runner wrote stderr: ${describeBytes(standard.stderr)}`);
  }
  const text = standard.stdout.toString("utf8");
  let parsed;
  try {
    parsed = JSON.parse(text);
  } catch (error) {
    throw new Error(`${config.moduleName}.${config.entry} standard ABI serializer did not return JSON: ${text}`);
  }
  return layout.normalize(parsed);
}

function runWasmAbi(config, paths, shortEntry, layout, expected) {
  const plan = new HostPlan();
  wasmAbiArgs(config).forEach((arg) => materializeArgPlan(plan, arg));
  const result = host.script(
    paths.wasm,
    plan.commands,
    shortEntry,
    layout.publicSlots,
    resultReadCommands(layout, expected),
  );
  return decodePublicValue(layout, result.memoryChunks, result.slots);
}

function describeBytes(bytes) {
  const text = bytes.toString("utf8");
  if (/^[\x09\x0a\x0d\x20-\x7e]*$/.test(text)) {
    return JSON.stringify(text);
  }
  return `0x${bytes.toString("hex")}`;
}

let irComparisonCount = 0;

function runIR(config, fullEntry) {
  const args = [leanExe, "eval-ir", "--module", config.moduleName, "--entry", fullEntry];
  for (const value of config.programArgs) {
    args.push(BigInt.asUintN(64, BigInt(value)).toString());
  }
  const result = run(args, { encoding: null, timeout: 10000 });
  if (result.status === 3) {
    return null;
  }
  requireSuccess(result, `${leanExe} ${args.slice(1).join(" ")}`);
  return result.stdout || Buffer.alloc(0);
}

function compareIRResult(config, fullEntry, wasm) {
  const irStdout = runIR(config, fullEntry);
  if (irStdout === null) {
    return false;
  }
  if (Buffer.compare(irStdout, wasm.stdout) !== 0) {
    throw new Error(
      `${config.moduleName}.${config.entry} IR interpreter differs:\n` +
        `stdout: wasm ${describeBytes(wasm.stdout)}, ir ${describeBytes(irStdout)}`,
    );
  }
  irComparisonCount += 1;
  return true;
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
    resultLayout: null,
    abiArgs: null,
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
  if (config.mode === "pure-abi") {
    const layout = resolveLayout(config.resultLayout);
    const expected = parseStandardAbiValue(config, standard, layout);
    const actual = runWasmAbi(config, paths, shortEntry, layout, expected);
    assertAbiEqual(`${config.moduleName}.${config.entry}`, "result", actual, expected);
    cleanup(config, paths);
    process.stdout.write(`matched ${config.mode} ${fullEntry}\n`);
    return;
  }
  const wasm = runWasm(config, paths, shortEntry);
  compareResults(config, standard, wasm);
  const irMatched =
    config.mode === "pure" && wasm.status === 0 && compareIRResult(config, fullEntry, wasm);

  cleanup(config, paths);
  process.stdout.write(`matched ${config.mode} ${fullEntry}\n`);
  if (irMatched) {
    process.stdout.write(`matched ir ${fullEntry}\n`);
  }
}

function cleanup(config, paths) {
  if (config.keep) {
    return;
  }
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

function selfTest() {
  const correctness = "LeanExe.Examples.Correctness";
  const clob = "LeanExe.Examples.Clob";
  const u64Layout = scalarLayout("UInt64");
  const natLayout = scalarLayout("Nat");
  const optionNatLayout = variantLayout([[], [u64Layout]]);
  const orderLayout = structLayout([
    ["id", u64Layout],
    ["trader", u64Layout],
    ["side", u64Layout],
    ["price", u64Layout],
    ["qty", u64Layout],
  ]);
  const orderArrayLayout = arrayLayout(orderLayout);
  const tradeLayout = structLayout([
    ["takerId", u64Layout],
    ["makerId", u64Layout],
    ["price", u64Layout],
    ["qty", u64Layout],
  ]);
  const tradeArrayLayout = arrayLayout(tradeLayout);
  const opResultLayout = structLayout([
    ["status", u64Layout],
    ["book", orderArrayLayout],
    ["trades", tradeArrayLayout],
  ]);
  const matchStateLayout = structLayout([
    ["book", orderArrayLayout],
    ["trades", tradeArrayLayout],
    ["remaining", u64Layout],
  ]);
  const levelLayout = structLayout([
    ["price", u64Layout],
    ["qty", u64Layout],
  ]);
  const levelArrayLayout = arrayLayout(levelLayout);
  const depthLayout = structLayout([
    ["bids", levelArrayLayout],
    ["asks", levelArrayLayout],
  ]);
  const nestedU64ArrayLayout = arrayLayout(arrayLayout(u64Layout));
  const byteArrayArrayLayout = arrayLayout(byteArrayLayout);
  const optionArrayByteArrayLayout = variantLayout([[], [byteArrayArrayLayout]]);
  const exceptByteArrayArrayLayout = variantLayout([[byteArrayLayout], [byteArrayArrayLayout]]);
  const optionByteArrayLayout = variantLayout([[], [byteArrayLayout]]);
  const exceptByteArrayByteArrayLayout = variantLayout([[byteArrayLayout], [byteArrayLayout]]);
  const optionByteArrayArrayLayout = arrayLayout(optionByteArrayLayout);
  const exceptByteArrayByteArrayArrayLayout = arrayLayout(exceptByteArrayByteArrayLayout);
  const optionArrayOptionByteArrayLayout = variantLayout([[], [optionByteArrayArrayLayout]]);
  const tokenLayout = variantLayout([[byteArrayLayout], [u64Layout]]);
  const tokenArrayLayout = arrayLayout(tokenLayout);
  const arrayBoxLayout = structLayout([
    ["values", arrayLayout(u64Layout)],
    ["count", u64Layout],
  ]);
  const recArrayStateLayout = structLayout([
    ["values", arrayLayout(u64Layout)],
    ["marker", u64Layout],
  ]);
  const pointLayout = structLayout([
    ["x", u64Layout],
    ["y", u64Layout],
  ]);
  const byteArrayGroupLayout = structLayout([
    ["values", byteArrayArrayLayout],
    ["marker", u64Layout],
  ]);
  const byteArrayGroupArrayLayout = arrayLayout(byteArrayGroupLayout);
  const nestedU64ArraySample = [[1, 2], [3, 4, 5]];
  const nestedU64ArrayAltSample = [[], [9], [10, 11]];
  const byteArrayArraySample = [[65], [66, 67], [68, 69, 70]];
  const byteArrayArrayAltSample = [[87], [88, 89], [90]];
  const optionByteArrayArraySample = [
    { tag: 1, fields: [[65]] },
    { tag: 0, fields: [] },
    { tag: 1, fields: [[66, 67]] },
  ];
  const exceptByteArrayByteArrayArraySample = [
    { tag: 1, fields: [[65]] },
    { tag: 0, fields: [[66, 67]] },
    { tag: 1, fields: [[68, 69, 70]] },
  ];
  const nestedTaggedArraySample = {
    tag: 1,
    fields: [optionByteArrayArraySample],
  };
  const nestedTaggedArrayNoneSample = {
    tag: 0,
    fields: [],
  };
  const exceptArrayOkSample = {
    tag: 1,
    fields: [[[65], [66, 67]]],
  };
  const exceptArrayErrorSample = {
    tag: 0,
    fields: [[69, 82, 82]],
  };
  const tokenArraySample = [
    { tag: 0, fields: [[65]] },
    { tag: 1, fields: [7] },
    { tag: 0, fields: [[66, 67]] },
  ];
  const byteArrayGroupArraySample = [
    { values: [[65], [66, 67]], marker: 2 },
    { values: [[68]], marker: 3 },
  ];
  const renderUInt64Array = "(fun row => __leanexeJsonArray row __leanexeJsonUInt64)";
  const renderToken = `(fun token =>
  match token with
  | .text bytes =>
      let out := "{\\"tag\\":0,\\"fields\\":[".toUTF8
      let out := out ++ __leanexeJsonByteArray bytes
      (out.push (93 : UInt8)).push (125 : UInt8)
  | .number value =>
      let out := "{\\"tag\\":1,\\"fields\\":[".toUTF8
      let out := __leanexeAppendUInt64 out value
      (out.push (93 : UInt8)).push (125 : UInt8))`;
  const renderByteArrayGroup = `(fun group =>
  let out := "{\\"values\\":".toUTF8
  let out := out ++ __leanexeJsonArray group.values __leanexeJsonByteArray
  let out := out ++ ",\\"marker\\":".toUTF8
  let out := __leanexeAppendUInt64 out group.marker
  out.push (125 : UInt8))`;
  const renderOptionNat = `match __leanexeValue with
  | none => "{\\"tag\\":0,\\"fields\\":[]}".toUTF8
  | some value =>
      let out := "{\\"tag\\":1,\\"fields\\":[".toUTF8
      let out := __leanexeAppendNat out value
      (out.push (93 : UInt8)).push (125 : UInt8)`;
  const renderOrder = `(fun order =>
  let out := "{\\"id\\":".toUTF8
  let out := __leanexeAppendUInt64 out order.id
  let out := out ++ ",\\"trader\\":".toUTF8
  let out := __leanexeAppendUInt64 out order.trader
  let out := out ++ ",\\"side\\":".toUTF8
  let out := __leanexeAppendUInt64 out order.side
  let out := out ++ ",\\"price\\":".toUTF8
  let out := __leanexeAppendUInt64 out order.price
  let out := out ++ ",\\"qty\\":".toUTF8
  let out := __leanexeAppendUInt64 out order.qty
  out.push (125 : UInt8))`;
  const renderTrade = `(fun trade =>
  let out := "{\\"takerId\\":".toUTF8
  let out := __leanexeAppendUInt64 out trade.takerId
  let out := out ++ ",\\"makerId\\":".toUTF8
  let out := __leanexeAppendUInt64 out trade.makerId
  let out := out ++ ",\\"price\\":".toUTF8
  let out := __leanexeAppendUInt64 out trade.price
  let out := out ++ ",\\"qty\\":".toUTF8
  let out := __leanexeAppendUInt64 out trade.qty
  out.push (125 : UInt8))`;
  const renderOpResult = `let out := "{\\"status\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.status
let out := out ++ ",\\"book\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.book ${renderOrder}
let out := out ++ ",\\"trades\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.trades ${renderTrade}
out.push (125 : UInt8)`;
  const renderMatchState = `let out := "{\\"book\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.book ${renderOrder}
let out := out ++ ",\\"trades\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.trades ${renderTrade}
let out := out ++ ",\\"remaining\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.remaining
out.push (125 : UInt8)`;
  const renderLevel = `(fun level =>
  let out := "{\\"price\\":".toUTF8
  let out := __leanexeAppendUInt64 out level.price
  let out := out ++ ",\\"qty\\":".toUTF8
  let out := __leanexeAppendUInt64 out level.qty
  out.push (125 : UInt8))`;
  const renderDepth = `let out := "{\\"bids\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.bids ${renderLevel}
let out := out ++ ",\\"asks\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.asks ${renderLevel}
out.push (125 : UInt8)`;
  const order = (id, trader, side, price, qty = 1) => ({ id, trader, side, price, qty });
  const buy = order(90, 90, 0, 100, 5);
  const sell = order(91, 91, 1, 100, 5);
  const rejected = [
    order(1, 1, 0, 50),
    order(2, 90, 1, 90),
    order(3, 3, 1, 101),
  ];
  const buys = [
    order(1, 1, 1, 100),
    order(2, 2, 1, 99),
    order(3, 3, 1, 99),
    order(4, 4, 1, 100),
    order(5, 5, 0, 1),
  ];
  const sells = [
    order(1, 1, 0, 100),
    order(2, 2, 0, 101),
    order(3, 3, 0, 101),
    order(4, 4, 0, 99),
    order(5, 5, 1, 200),
    order(6, 91, 0, 200),
  ];
  const leanOrder = (value) =>
    `({ id := ${value.id}, trader := ${value.trader}, side := ${value.side}, ` +
      `price := ${value.price}, qty := ${value.qty} } : ${clob}.Order)`;
  const leanBook = (values) =>
    values.length === 0
      ? `(#[] : Array ${clob}.Order)`
      : `(#[${values.map(leanOrder).join(", ")}] : Array ${clob}.Order)`;
  const leanTrade = (value) =>
    `({ takerId := ${value.takerId}, makerId := ${value.makerId}, ` +
      `price := ${value.price}, qty := ${value.qty} } : ${clob}.Trade)`;
  const leanTrades = (values) =>
    values.length === 0
      ? `(#[] : Array ${clob}.Trade)`
      : `(#[${values.map(leanTrade).join(", ")}] : Array ${clob}.Trade)`;
  const leanMatchState = (value) =>
    `({ book := ${leanBook(value.book)}, trades := ${leanTrades(value.trades)}, ` +
      `remaining := ${value.remaining} } : ${clob}.MatchState)`;
  const opResultCases = (entry, values) => values.map(({ book, taker }) => ({
    mode: "pure-abi",
    moduleName: clob,
    entry,
    abiArgs: [
      { layout: orderArrayLayout, value: book },
      { layout: orderLayout, value: taker },
    ],
    standardCall: `${clob}.${entry} ${leanBook(book)} ${leanOrder(taker)}`,
    resultLayout: opResultLayout,
    serializer: renderOpResult,
  }));
  const findBestCases = [
    { book: [], taker: buy },
    { book: rejected, taker: buy },
    { book: [rejected[0], buys[0]], taker: buy },
    { book: buys, taker: buy },
    { book: sells, taker: sell },
  ].map(({ book, taker }) => ({
    mode: "pure-abi",
    moduleName: clob,
    entry: "findBest",
    abiArgs: [
      { layout: orderArrayLayout, value: book },
      { layout: orderLayout, value: taker },
    ],
    standardCall: `${clob}.findBest ${leanBook(book)} ${leanOrder(taker)}`,
    resultLayout: optionNatLayout,
    serializer: renderOptionNat,
  }));
  const baseBook = [order(1, 10, 0, 100, 5)];
  const postOnlyCases = opResultCases("postOnly", [
    { book: [], taker: order(0, 11, 1, 200) },
    { book: [], taker: order(2, 0, 1, 200) },
    { book: baseBook, taker: order(2, 11, 3, 200) },
    { book: baseBook, taker: order(2, 11, 1, 200, 0) },
    { book: baseBook, taker: order(1, 11, 1, 200) },
    { book: baseBook, taker: order(2, 11, 1, 100, 3) },
    { book: baseBook, taker: order(2, 11, 1, 105, 3) },
  ]);
  const matchFuelCases = [
    { fuel: 0, taker: order(2, 11, 1, 100, 3), state: { book: baseBook, trades: [], remaining: 3 } },
    { fuel: 2, taker: order(2, 11, 1, 100, 3), state: { book: baseBook, trades: [], remaining: 0 } },
    { fuel: 2, taker: order(2, 11, 1, 100, 3), state: { book: [], trades: [], remaining: 3 } },
    { fuel: 1, taker: order(2, 11, 1, 100, 7), state: { book: baseBook, trades: [], remaining: 7 } },
    { fuel: 2, taker: order(2, 11, 1, 100, 3), state: { book: baseBook, trades: [], remaining: 3 } },
  ].map(({ fuel, taker, state }) => ({
    mode: "pure-abi",
    moduleName: clob,
    entry: "matchFuel",
    abiArgs: [
      { layout: natLayout, value: fuel },
      { layout: orderLayout, value: taker },
      { layout: matchStateLayout, value: state },
    ],
    standardCall: `${clob}.matchFuel ${fuel} ${leanOrder(taker)} ${leanMatchState(state)}`,
    resultLayout: matchStateLayout,
    serializer: renderMatchState,
  }));
  const twoMakerBook = [
    order(1, 10, 0, 100, 2),
    order(2, 12, 0, 101, 3),
  ];
  const limitCases = opResultCases("limit", [
    { book: baseBook, taker: order(1, 11, 1, 100, 3) },
    { book: baseBook, taker: order(2, 11, 1, 100, 5) },
    { book: baseBook, taker: order(2, 11, 1, 100, 3) },
    { book: baseBook, taker: order(2, 11, 1, 100, 7) },
    { book: baseBook, taker: order(2, 11, 1, 105, 3) },
    { book: twoMakerBook, taker: order(3, 13, 1, 100, 5) },
  ]);
  const marketCases = opResultCases("market", [
    { book: baseBook, taker: order(0, 11, 1, 999, 3) },
    { book: [order(1, 10, 1, 500, 5)], taker: order(2, 11, 0, 0, 3) },
    { book: [order(1, 10, 0, 1, 5)], taker: order(2, 11, 1, 999, 3) },
    { book: baseBook, taker: order(2, 11, 1, 999, 9) },
    { book: baseBook, taker: order(2, 10, 1, 999, 3) },
  ]);
  const depthBook = [
    order(1, 10, 0, 100, 2),
    order(2, 11, 1, 105, 4),
    order(3, 12, 0, 99, 7),
    order(4, 13, 0, 100, 3),
    order(5, 14, 1, 104, 6),
    order(6, 15, 1, 105, 1),
    order(7, 16, 2, 777, 9),
  ];
  const depthCases = [[], depthBook].map((book) => ({
    mode: "pure-abi",
    moduleName: clob,
    entry: "depth",
    abiArgs: [{ layout: orderArrayLayout, value: book }],
    standardCall: `${clob}.depth ${leanBook(book)}`,
    resultLayout: depthLayout,
    serializer: renderDepth,
  }));
  const recArrayStateCase = {
    mode: "pure-abi",
    moduleName: correctness,
    entry: "recArrayStateFuel",
    abiArgs: [
      { layout: natLayout, value: 2 },
      { layout: recArrayStateLayout, value: { values: [], marker: 7 } },
    ],
    standardCall:
      `${correctness}.recArrayStateFuel 2 ` +
        `({ values := #[], marker := 7 } : ${correctness}.RecArrayState)`,
    resultLayout: recArrayStateLayout,
    serializer: `let out := "{\\"values\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.values __leanexeJsonUInt64
let out := out ++ ",\\"marker\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.marker
out.push (125 : UInt8)`,
  };
  const cases = [
    ...findBestCases,
    ...postOnlyCases,
    ...matchFuelCases,
    ...limitCases,
    ...marketCases,
    ...depthCases,
    recArrayStateCase,
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
      entry: "idFunctionUInt64",
      programArgs: ["0"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "shortOrSkipsTrap",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "shortAndSkipsTrap",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "divByZero",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "modByZero",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "overflow",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "underflow",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natSubSaturates",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natSubNormal",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natAddNormal",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natMulNormal",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
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
      entry: "natDivModNormal",
      programArgs: ["8"],
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natDivModZero",
      programArgs: ["7"],
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natSuccPred",
      programArgs: ["0"],
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natSuccPred",
      programArgs: ["5"],
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "bitwiseOrXor",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "complementNotation",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "shiftMasking",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8ShiftNotation",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8DirectShift",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint64OfNatValue",
      programArgs: ["41"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint64OfHugeNat",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "natToUInt64Huge",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint64ToNatMethodMax",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8ParamToNat",
      programArgs: ["300"],
      standardCall: `${correctness}.uint8ParamToNat (300 : UInt8)`,
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8Return",
      resultSlots: "#[UInt8.toUInt64 __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8AddWrap",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8SubWrap",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8MulWrap",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint8DivModZero",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint32ParamToNat",
      programArgs: ["4294967297"],
      standardCall: `${correctness}.uint32ParamToNat (4294967297 : UInt32)`,
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint32Return",
      resultSlots: "#[UInt32.toUInt64 __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint32DivMod",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "uint32DivModZero",
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
      entry: "structureReturn",
      programArgs: ["0"],
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
      entry: "typeclassSameUInt64",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassSameCustomBEq",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassDefaultUInt64",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassDefaultPoint",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScoreUInt64",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScorePoint",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScoreOptionUInt64",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScoreArrayTotalDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScoreArrayAnyDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScoreArrayFindDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScoreListFoldlDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "typeclassScoreListFindDemo",
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
      entry: "statusBranchReturn",
      programArgs: ["1"],
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
      entry: "statusParam",
      programArgs: ["1", "0", "7"],
      standardCall: `${correctness}.statusParam (${correctness}.Status.error 7)`,
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionReturn",
      programArgs: ["0"],
      resultSlots:
        "match __leanexeValue with | none => #[0, 0] | some value => #[1, value]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionReturn",
      programArgs: ["3"],
      resultSlots:
        "match __leanexeValue with | none => #[0, 0] | some value => #[1, value]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionParam",
      programArgs: ["0", "44"],
      standardCall: `${correctness}.optionParam (none : Option UInt64)`,
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionParam",
      programArgs: ["1", "5"],
      standardCall: `${correctness}.optionParam (some (5 : UInt64))`,
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptReturn",
      programArgs: ["0"],
      resultSlots:
        "match __leanexeValue with | Except.error code => #[0, code, 0] | Except.ok value => #[1, 0, value]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptReturn",
      programArgs: ["3"],
      resultSlots:
        "match __leanexeValue with | Except.error code => #[0, code, 0] | Except.ok value => #[1, 0, value]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptParam",
      programArgs: ["0", "7", "0"],
      standardCall: `${correctness}.exceptParam (Except.error (7 : UInt64) : Except UInt64 UInt64)`,
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptParam",
      programArgs: ["1", "0", "5"],
      standardCall: `${correctness}.exceptParam (Except.ok (5 : UInt64) : Except UInt64 UInt64)`,
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
      entry: "arrayFoldrDigits",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayFoldrWindow",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayFoldrStartClamps",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayGetDRead",
      programArgs: ["1"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayGetDRead",
      programArgs: ["2"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayGetQuestionRead",
      programArgs: ["1"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayGetQuestionRead",
      programArgs: ["2"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayFilterScalarsRead",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayFilterWindowRead",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayFilterNoneSize",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayUInt8Read",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayUInt8SetRead",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayUInt32MapRead",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayBoolRead",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayNatRead",
      resultSlots: "#[UInt64.ofNat __leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "arrayStructureFoldRead",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "leanListScenarioScore",
      programArgs: ["0", "7"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "leanListScenarioScore",
      programArgs: ["1", "7"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "leanListScenarioScore",
      programArgs: ["2", "2"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "leanListScenarioScore",
      programArgs: ["3", "99"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "leanPairListLookupDemo",
      programArgs: ["7"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "leanPairListLookupDemo",
      programArgs: ["2"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "leanPairListLookupDemo",
      programArgs: ["5"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinaryScenarioScore",
      programArgs: ["0", "5"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinaryScenarioScore",
      programArgs: ["0", "9"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinaryScenarioScore",
      programArgs: ["1", "4"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinaryScenarioScore",
      programArgs: ["2", "9"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinarySharedChildScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinaryReturnedSubtreeAliasScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinarySharedArrayScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinarySharedStructAliasScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "u64BinarySharedTaggedAliasScore",
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
      mode: "pure",
      moduleName: correctness,
      entry: "matchedScalarScore",
      programArgs: ["0"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "matchedScalarScore",
      programArgs: ["1"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "matchedScalarSkipsUnusedBranchField",
      programArgs: ["0"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "matchedScalarSkipsUnusedBranchField",
      programArgs: ["1"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "matchedFindIdxPoint",
      programArgs: ["2"],
      resultLayout: pointLayout,
      serializer: `let out := "{\\"x\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.x
let out := out ++ ",\\"y\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.y
out.push (125 : UInt8)`,
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "matchedFindIdxPoint",
      programArgs: ["9"],
      resultLayout: pointLayout,
      serializer: `let out := "{\\"x\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.x
let out := out ++ ",\\"y\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.y
out.push (125 : UInt8)`,
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "matchedFindIdxArray",
      programArgs: ["2"],
      resultLayout: arrayLayout(u64Layout),
      serializer: "__leanexeJsonArray __leanexeValue __leanexeJsonUInt64",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "matchedFindIdxArray",
      programArgs: ["9"],
      resultLayout: arrayLayout(u64Layout),
      serializer: "__leanexeJsonArray __leanexeValue __leanexeJsonUInt64",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "structureArrayReturn",
      resultLayout: arrayBoxLayout,
      serializer: `let out := "{\\"values\\":".toUTF8
let out := out ++ __leanexeJsonArray __leanexeValue.values __leanexeJsonUInt64
let out := out ++ ",\\"count\\":".toUTF8
let out := __leanexeAppendUInt64 out __leanexeValue.count
out.push (125 : UInt8)`,
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicByteArrayArrayReturn",
      resultLayout: byteArrayArrayLayout,
      serializer: "__leanexeJsonArray __leanexeValue __leanexeJsonByteArray",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicOptionArrayParam",
      abiArgs: [{ layout: optionArrayByteArrayLayout, value: { tag: 1, fields: [byteArrayArraySample] } }],
      standardCall:
        `${correctness}.publicOptionArrayParam (some (#["A".toUTF8, "BC".toUTF8, "DEF".toUTF8] : Array ByteArray))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicOptionArrayParam",
      abiArgs: [{ layout: optionArrayByteArrayLayout, value: { tag: 0, fields: [] } }],
      standardCall:
        `${correctness}.publicOptionArrayParam (none : Option (Array ByteArray))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicExceptArrayParam",
      abiArgs: [{ layout: exceptByteArrayArrayLayout, value: exceptArrayOkSample }],
      standardCall:
        `${correctness}.publicExceptArrayParam (Except.ok (#["A".toUTF8, "BC".toUTF8] : Array ByteArray) : Except ByteArray (Array ByteArray))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicExceptArrayParam",
      abiArgs: [{ layout: exceptByteArrayArrayLayout, value: exceptArrayErrorSample }],
      standardCall:
        `${correctness}.publicExceptArrayParam (Except.error ("ERR".toUTF8) : Except ByteArray (Array ByteArray))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicOptionByteArrayArrayParam",
      abiArgs: [{ layout: optionByteArrayArrayLayout, value: optionByteArrayArraySample }],
      standardCall:
        `${correctness}.publicOptionByteArrayArrayParam (#[(some ("A".toUTF8) : Option ByteArray), (none : Option ByteArray), (some ("BC".toUTF8) : Option ByteArray)] : Array (Option ByteArray))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicExceptByteArrayArrayParam",
      abiArgs: [{ layout: exceptByteArrayByteArrayArrayLayout, value: exceptByteArrayByteArrayArraySample }],
      standardCall:
        `${correctness}.publicExceptByteArrayArrayParam (#[(Except.ok ("A".toUTF8) : Except ByteArray ByteArray), (Except.error ("BC".toUTF8) : Except ByteArray ByteArray), (Except.ok ("DEF".toUTF8) : Except ByteArray ByteArray)] : Array (Except ByteArray ByteArray))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicNestedTaggedArrayParam",
      abiArgs: [{ layout: optionArrayOptionByteArrayLayout, value: nestedTaggedArraySample }],
      standardCall:
        `${correctness}.publicNestedTaggedArrayParam (some (#[(some ("A".toUTF8) : Option ByteArray), (none : Option ByteArray), (some ("BC".toUTF8) : Option ByteArray)] : Array (Option ByteArray)))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicNestedTaggedArrayParam",
      abiArgs: [{ layout: optionArrayOptionByteArrayLayout, value: nestedTaggedArrayNoneSample }],
      standardCall:
        `${correctness}.publicNestedTaggedArrayParam (none : Option (Array (Option ByteArray)))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicNestedArrayParam",
      abiArgs: [{ layout: nestedU64ArrayLayout, value: nestedU64ArraySample }],
      standardCall:
        `${correctness}.publicNestedArrayParam (#[#[1, 2], #[3, 4, 5]] : Array (Array UInt64))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicNestedArrayParam",
      abiArgs: [{ layout: nestedU64ArrayLayout, value: nestedU64ArrayAltSample }],
      standardCall:
        `${correctness}.publicNestedArrayParam (#[#[], #[9], #[10, 11]] : Array (Array UInt64))`,
      resultLayout: u64Layout,
      serializer: "__leanexeJsonUInt64 __leanexeValue",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicNestedArrayOpsReturn",
      abiArgs: [{ layout: nestedU64ArrayLayout, value: nestedU64ArraySample }],
      standardCall:
        `${correctness}.publicNestedArrayOpsReturn (#[#[1, 2], #[3, 4, 5]] : Array (Array UInt64))`,
      resultLayout: nestedU64ArrayLayout,
      serializer: `__leanexeJsonArray __leanexeValue ${renderUInt64Array}`,
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicByteArrayArrayOpsReturn",
      abiArgs: [{ layout: byteArrayArrayLayout, value: byteArrayArraySample }],
      standardCall:
        `${correctness}.publicByteArrayArrayOpsReturn #["A".toUTF8, "BC".toUTF8, "DEF".toUTF8]`,
      resultLayout: byteArrayArrayLayout,
      serializer: "__leanexeJsonArray __leanexeValue __leanexeJsonByteArray",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicByteArrayArrayOpsReturn",
      abiArgs: [{ layout: byteArrayArrayLayout, value: byteArrayArrayAltSample }],
      standardCall:
        `${correctness}.publicByteArrayArrayOpsReturn #["W".toUTF8, "XY".toUTF8, "Z".toUTF8]`,
      resultLayout: byteArrayArrayLayout,
      serializer: "__leanexeJsonArray __leanexeValue __leanexeJsonByteArray",
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicTokenArrayReturn",
      resultLayout: tokenArrayLayout,
      serializer: `__leanexeJsonArray __leanexeValue ${renderToken}`,
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicTokenArrayOpsReturn",
      abiArgs: [{ layout: tokenArrayLayout, value: tokenArraySample }],
      standardCall:
        `${correctness}.publicTokenArrayOpsReturn #[${correctness}.PublicToken.text "A".toUTF8, ${correctness}.PublicToken.number 7, ${correctness}.PublicToken.text "BC".toUTF8]`,
      resultLayout: tokenArrayLayout,
      serializer: `__leanexeJsonArray __leanexeValue ${renderToken}`,
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicByteArrayGroupArrayReturn",
      resultLayout: byteArrayGroupArrayLayout,
      serializer: `__leanexeJsonArray __leanexeValue ${renderByteArrayGroup}`,
    },
    {
      mode: "pure-abi",
      moduleName: correctness,
      entry: "publicByteArrayGroupArrayFullOpsReturn",
      abiArgs: [{ layout: byteArrayGroupArrayLayout, value: byteArrayGroupArraySample }],
      standardCall: `${correctness}.publicByteArrayGroupArrayFullOpsReturn (#[
  { values := #["A".toUTF8, "BC".toUTF8], marker := (2 : UInt64) },
  { values := #["D".toUTF8], marker := (3 : UInt64) }
] : Array ${correctness}.ByteArrayGroup)`,
      resultLayout: byteArrayGroupArrayLayout,
      serializer: `__leanexeJsonArray __leanexeValue ${renderByteArrayGroup}`,
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
      entry: "arrayFoldrByteArrayAccumulator",
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
      entry: "exceptForArrayErrorSkipsRestTrap",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok value => __leanexeAppendUInt64 "ok".toUTF8 value`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionForByteArrayNoneSkipsRestTrap",
      serializer: `match __leanexeValue with
| some value => __leanexeAppendUInt64 ByteArray.empty value
| none => "none".toUTF8`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptForRangeBreakSum",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok value => __leanexeAppendUInt64 "ok".toUTF8 value`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionForArrayContinueSum",
      serializer: `match __leanexeValue with
| some value => __leanexeAppendUInt64 ByteArray.empty value
| none => "none".toUTF8`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionWhileSum",
      serializer: `match __leanexeValue with
| some value => __leanexeAppendUInt64 ByteArray.empty value
| none => "none".toUTF8`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionForByteArrayOutput",
      serializer: `match __leanexeValue with
| some bytes => bytes
| none => "none".toUTF8`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionForByteArrayOutputNoneSkipsRestTrap",
      serializer: `match __leanexeValue with
| some bytes => bytes
| none => "none".toUTF8`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptForByteArrayOutput",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok bytes => bytes`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptForByteArrayOutputErrorSkipsRestTrap",
      serializer: `match __leanexeValue with
| Except.error code => __leanexeAppendUInt64 ByteArray.empty code
| Except.ok bytes => bytes`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionForByteArrayState",
      serializer: `match __leanexeValue with
| some state =>
    let out := __leanexeAppendUInt64 ByteArray.empty state.count
    let out := __leanexeSep out
    out ++ state.bytes
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
      mode: "pure",
      moduleName: correctness,
      entry: "leanListConcatDirectDemo",
      programArgs: ["4"],
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListScenarioReverseValue",
      programArgs: ["0"],
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListScenarioReverseValue",
      programArgs: ["1"],
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListScenarioReverseValue",
      programArgs: ["3"],
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListScenarioAppendMapValue",
      programArgs: ["0"],
      serializer: `${correctness}.leanListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "leanListScenarioAppendMapValue",
      programArgs: ["2"],
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
      entry: "pointListMapValue",
      serializer: `${correctness}.pointListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "pointListFilterValue",
      serializer: `${correctness}.pointListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "pointListFindValue",
      serializer: `${correctness}.pointOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "pointListAppendReverseValue",
      serializer: `${correctness}.pointListBytes __leanexeValue`,
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "pointListFoldlScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "pointListFoldrScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "pointListAnyDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "pointListAllDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "statusListMapValue",
      serializer: `${correctness}.statusListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "statusListFilterValue",
      serializer: `${correctness}.statusListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "statusListFindValue",
      serializer: `${correctness}.statusOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "statusListAppendReverseValue",
      serializer: `${correctness}.statusListBytes __leanexeValue`,
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "statusListFoldlScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "statusListFoldrScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "statusListAnyDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "statusListAllDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayListMapValue",
      serializer: `${correctness}.byteArrayListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayListFilterValue",
      serializer: `${correctness}.byteArrayListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayListFindValue",
      serializer: `${correctness}.byteArrayOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayListAppendReverseValue",
      serializer: `${correctness}.byteArrayListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayListFoldlValue",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "byteArrayListFoldrValue",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "byteArrayListAnyDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "byteArrayListAllDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListMapValue",
      serializer: `${correctness}.optionByteArrayListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListFilterValue",
      serializer: `${correctness}.optionByteArrayListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListFindValue",
      serializer: `${correctness}.optionOptionByteArrayBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListAppendReverseValue",
      serializer: `${correctness}.optionByteArrayListBytes __leanexeValue`,
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionByteArrayListAnyDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionByteArrayListAllDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListFoldlValue",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListFoldrValue",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListFoldlStateValue",
      serializer: `${correctness}.byteOutputStateBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionByteArrayListFoldlTaggedAccumulatorValue",
      serializer: `${correctness}.optionByteArrayBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListMapValue",
      serializer: `${correctness}.exceptByteArrayUInt64ListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListFilterValue",
      serializer: `${correctness}.exceptByteArrayUInt64ListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListFindValue",
      serializer: `${correctness}.optionExceptByteArrayUInt64Bytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListAppendReverseValue",
      serializer: `${correctness}.exceptByteArrayUInt64ListBytes __leanexeValue`,
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListAnyDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListAllDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListFoldlValue",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListFoldrValue",
      serializer: "__leanexeValue",
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListFoldlStateValue",
      serializer: `${correctness}.byteOutputStateBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "exceptByteArrayUInt64ListFoldlTaggedAccumulatorValue",
      serializer: `${correctness}.exceptByteArrayByteArrayBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionUInt64ListMapValue",
      serializer: `${correctness}.optionUInt64ListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionUInt64ListFilterValue",
      serializer: `${correctness}.optionUInt64ListBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionUInt64ListFindValue",
      serializer: `${correctness}.optionOptionUInt64Bytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "optionUInt64ListAppendReverseValue",
      serializer: `${correctness}.optionUInt64ListBytes __leanexeValue`,
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionUInt64ListFoldlScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionUInt64ListFoldrScore",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionUInt64ListAnyDemo",
      resultSlots: "#[__leanexeValue]",
    },
    {
      mode: "pure",
      moduleName: correctness,
      entry: "optionUInt64ListAllDemo",
      resultSlots: "#[__leanexeValue]",
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
      entry: "u64BinaryScenarioValue",
      programArgs: ["0"],
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryScenarioValue",
      programArgs: ["1"],
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryScenarioValue",
      programArgs: ["2"],
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
      entry: "u64BinaryScenarioMirrorValue",
      programArgs: ["2"],
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryScenarioMirrorValue",
      programArgs: ["3"],
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
      entry: "u64BinaryScenarioFindValue",
      programArgs: ["0", "5"],
      serializer: `${correctness}.u64BinaryOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryScenarioFindValue",
      programArgs: ["1", "3"],
      serializer: `${correctness}.u64BinaryOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryScenarioFindValue",
      programArgs: ["1", "9"],
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
      entry: "u64BinaryScenarioRequireByteErrorValue",
      programArgs: ["2", "2"],
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryScenarioRequireByteErrorValue",
      programArgs: ["2", "9"],
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryOptionMapValue",
      programArgs: ["1", "3"],
      serializer: `${correctness}.u64BinaryOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryOptionMapValue",
      programArgs: ["1", "9"],
      serializer: `${correctness}.u64BinaryOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryExceptMapValue",
      programArgs: ["1", "3"],
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryExceptMapValue",
      programArgs: ["1", "9"],
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryExceptBindValue",
      programArgs: ["1", "1"],
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryExceptBindValue",
      programArgs: ["0", "1"],
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryExceptBindValue",
      programArgs: ["2", "0"],
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
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
      entry: "u64BinaryBoxFlowValue",
      programArgs: ["2", "0"],
      serializer: `${correctness}.u64BinaryBoxBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryBoxFlowValue",
      programArgs: ["2", "1"],
      serializer: `${correctness}.u64BinaryBoxBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryPairSlotFlowValue",
      programArgs: ["0"],
      serializer: `${correctness}.u64BinaryPairSlotBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryPairSlotFlowValue",
      programArgs: ["1"],
      serializer: `${correctness}.u64BinaryPairSlotBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryArrayFlowValue",
      programArgs: ["0"],
      serializer: `${correctness}.u64BinaryArrayBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryArrayFlowValue",
      programArgs: ["1"],
      serializer: `${correctness}.u64BinaryArrayBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryLoopGrowValue",
      serializer: `${correctness}.u64BinaryBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryLoopOptionValue",
      serializer: `${correctness}.u64BinaryOptionBytes __leanexeValue`,
    },
    {
      mode: "pure-bytes",
      moduleName: correctness,
      entry: "u64BinaryLoopExceptValue",
      serializer: `${correctness}.u64BinaryByteErrorExceptBytes __leanexeValue`,
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
      mode: "stdin",
      moduleName: "LeanExe.Examples.ByteArrayPrograms",
      entry: "appendBang",
      input: Buffer.from("", "utf8"),
      maxInputBytes: 8,
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.ByteArrayPrograms",
      entry: "tailSlice",
      input: Buffer.from("ABC", "utf8"),
      maxInputBytes: 8,
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.ByteArrayPrograms",
      entry: "tailSlice",
      input: Buffer.from("", "utf8"),
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
      input: Buffer.from(" [ 0 , 42 , 56 ] ", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonGcd",
      entry: "transform",
      input: Buffer.from("[]", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonGcd",
      entry: "transform",
      input: Buffer.from("[4,\"x\"]", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonTypedDecode",
      entry: "transform",
      input: Buffer.from("{\"values\":[6,10,14],\"multiplier\":2,\"includeCount\":true}", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonTypedDecode",
      entry: "transform",
      input: Buffer.from("{\"values\":[5,7],\"multiplier\":3,\"includeCount\":false}", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonTypedDecode",
      entry: "transform",
      input: Buffer.from("{\"values\":[1],\"values\":[2],\"multiplier\":2,\"includeCount\":true}", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonObjectArrayDecode",
      entry: "transform",
      input: Buffer.from("{\"items\":[{\"id\":1,\"weight\":4},{\"id\":2,\"weight\":7}],\"scale\":3}", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonObjectArrayDecode",
      entry: "transform",
      input: Buffer.from("{\"items\":[],\"scale\":9}", "utf8"),
    },
    {
      mode: "stdin-except",
      moduleName: "LeanExe.Examples.JsonObjectArrayDecode",
      entry: "transform",
      input: Buffer.from("{\"items\":[{\"id\":1}],\"scale\":3}", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonAdd",
      entry: "transform",
      input: Buffer.from("{\"a\":19,\"b\":23}", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonAdd",
      entry: "transform",
      input: Buffer.from(" { \"b\" : 1 , \"a\" : 2 } ", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonAdd",
      entry: "transform",
      input: Buffer.from("{\"a\":18446744073709551615,\"b\":1}", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonCollatzLength",
      entry: "transform",
      input: Buffer.from("{\"collatzLengthFor\":41}", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonCollatzLength",
      entry: "transform",
      input: Buffer.from(" { \"collatzLengthFor\" : 7 } ", "utf8"),
    },
    {
      mode: "stdin",
      moduleName: "LeanExe.Examples.JsonCollatzLength",
      entry: "transform",
      input: Buffer.from("{\"collatzLengthFor\":0}", "utf8"),
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
    {
      mode: "argv-except",
      moduleName: "LeanExe.Examples.ByteArrayPrograms",
      entry: "argvFirstLast",
      programArgs: [],
    },
  ];
  for (const testCase of cases) {
    compareCase(testCase);
  }
  process.stdout.write(`checked ${cases.length} standard Lean comparison cases\n`);
  process.stdout.write(`checked ${irComparisonCount} IR interpreter comparison cases\n`);
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
      resultLayout: config.resultLayout,
      abiArgs: config.abiArgs,
      keep: config.keep,
    });
  }
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
