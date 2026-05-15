#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const correctnessModule = "LeanExe.Examples.Correctness";
const byteArrayModule = "LeanExe.Examples.ByteArrayPrograms";
const jsonGcdModule = "LeanExe.Examples.JsonGcd";
const jsonTreeModule = "LeanExe.Examples.JsonTreeCommand";
const jsonMergeTreeModule = "LeanExe.Examples.JsonMergeTreeCommand";
const jsonGcTreeRewriteModule = "LeanExe.Examples.JsonGcTreeRewrite";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const outDir = path.join(".lake", "build", "wasi-programs");

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

function bytes(text) {
  return Buffer.from(text, "utf8");
}

function compileStdout(entry) {
  const out = path.join(outDir, `${entry}.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi",
    "--module",
    correctnessModule,
    "--entry",
    `${correctnessModule}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed to compile`);
  }
  return out;
}

function compileStdin(moduleName, entry, maxInputBytes) {
  const out = path.join(outDir, `${entry}.stdin.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi-stdin",
    "--max-input-bytes",
    maxInputBytes.toString(),
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed to compile`);
  }
  return out;
}

function compileStdinExcept(moduleName, entry, maxInputBytes) {
  const out = path.join(outDir, `${entry}.stdin-except.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi-stdin-except",
    "--max-input-bytes",
    maxInputBytes.toString(),
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed to compile`);
  }
  return out;
}

function compileArgvExcept(moduleName, entry, maxArgs, maxArgBytes) {
  const out = path.join(outDir, `${entry}.argv-except.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi-argv-except",
    "--max-args",
    maxArgs.toString(),
    "--max-argv-bytes",
    maxArgBytes.toString(),
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed to compile`);
  }
  return out;
}

function compileStdinArgvExcept(moduleName, entry, maxInputBytes, maxArgs, maxArgBytes) {
  const out = path.join(outDir, `${entry}.stdin-argv-except.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi-stdin-argv-except",
    "--max-input-bytes",
    maxInputBytes.toString(),
    "--max-args",
    maxArgs.toString(),
    "--max-argv-bytes",
    maxArgBytes.toString(),
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed to compile`);
  }
  return out;
}

function expectProgram(entry, expectedBytes) {
  const wasm = compileStdout(entry);
  const result = run([wasmtime, "run", wasm]);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed in Wasmtime`);
  }
  const expected = Buffer.from(expectedBytes);
  const actual = result.stdout || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`${entry}: expected ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
}

function runWasmtimeWithInput(wasm, entry, suffix, inputBytes) {
  const inputPath = path.join(outDir, `${entry}.${inputBytes.length}.${suffix}.stdin`);
  fs.writeFileSync(inputPath, Buffer.from(inputBytes));
  const inputFd = fs.openSync(inputPath, "r");
  try {
    return run([wasmtime, "run", wasm], {
      stdio: [inputFd, "pipe", "pipe"],
      timeout: 10000,
    });
  } finally {
    fs.closeSync(inputFd);
  }
}

function runWasmtimeWithInputAndArgs(wasm, entry, suffix, inputBytes, args) {
  const inputPath = path.join(outDir, `${entry}.${inputBytes.length}.${suffix}.stdin`);
  fs.writeFileSync(inputPath, Buffer.from(inputBytes));
  const inputFd = fs.openSync(inputPath, "r");
  try {
    return run([wasmtime, "run", wasm, ...args], {
      stdio: [inputFd, "pipe", "pipe"],
      timeout: 10000,
    });
  } finally {
    fs.closeSync(inputFd);
  }
}

function expectStdinProgram(moduleName, entry, maxInputBytes, inputBytes, expectedBytes) {
  const wasm = compileStdin(moduleName, entry, maxInputBytes);
  const result = runWasmtimeWithInput(wasm, entry, "ok", inputBytes);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed in Wasmtime`);
  }
  const expected = Buffer.from(expectedBytes);
  const actual = result.stdout || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`${entry}: expected ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
}

function expectStdinExceptOk(moduleName, entry, maxInputBytes, inputBytes, expectedBytes) {
  const wasm = compileStdinExcept(moduleName, entry, maxInputBytes);
  const result = runWasmtimeWithInput(wasm, entry, "except-ok", inputBytes);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed in Wasmtime`);
  }
  const expected = Buffer.from(expectedBytes);
  const actual = result.stdout || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`${entry}: expected stdout ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
  const stderr = result.stderr || Buffer.alloc(0);
  if (stderr.length !== 0) {
    throw new Error(`${entry}: expected empty stderr, got ${stderr.toString("hex")}`);
  }
}

function expectStdinExceptError(moduleName, entry, maxInputBytes, inputBytes, expectedBytes) {
  const wasm = compileStdinExcept(moduleName, entry, maxInputBytes);
  const result = runWasmtimeWithInput(wasm, entry, "except-error", inputBytes);
  if (result.status !== 1) {
    throw new Error(outputText(result).trim() || `${entry} should have exited with status 1`);
  }
  const expected = Buffer.from(expectedBytes);
  const actual = result.stderr || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`${entry}: expected stderr ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
  const stdout = result.stdout || Buffer.alloc(0);
  if (stdout.length !== 0) {
    throw new Error(`${entry}: expected empty stdout, got ${stdout.toString("hex")}`);
  }
}

function expectArgvExceptOk(moduleName, entry, maxArgs, maxArgBytes, args, expectedBytes) {
  const wasm = compileArgvExcept(moduleName, entry, maxArgs, maxArgBytes);
  const result = run([wasmtime, "run", wasm, ...args], {
    stdio: ["ignore", "pipe", "pipe"],
    timeout: 10000,
  });
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || `${entry} failed in Wasmtime`);
  }
  const expected = Buffer.from(expectedBytes);
  const actual = result.stdout || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`${entry}: expected stdout ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
  const stderr = result.stderr || Buffer.alloc(0);
  if (stderr.length !== 0) {
    throw new Error(`${entry}: expected empty stderr, got ${stderr.toString("hex")}`);
  }
}

function expectTreePipeline(inputBytes, needle, expectedBytes) {
  const makeTree = compileStdinExcept(jsonTreeModule, "makeTree", 4096);
  const searchTree = compileStdinArgvExcept(jsonTreeModule, "searchTree", 8192, 8, 256);
  const makeResult = runWasmtimeWithInput(makeTree, "makeTree", "tree", inputBytes);
  if (makeResult.status !== 0) {
    throw new Error(outputText(makeResult).trim() || "makeTree failed in Wasmtime");
  }
  const searchResult = runWasmtimeWithInputAndArgs(
    searchTree,
    "searchTree",
    `needle-${needle}`,
    makeResult.stdout || Buffer.alloc(0),
    [needle]
  );
  if (searchResult.status !== 0) {
    throw new Error(outputText(searchResult).trim() || "searchTree failed in Wasmtime");
  }
  const expected = Buffer.from(expectedBytes);
  const actual = searchResult.stdout || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`searchTree: expected stdout ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
  const stderr = searchResult.stderr || Buffer.alloc(0);
  if (stderr.length !== 0) {
    throw new Error(`searchTree: expected empty stderr, got ${stderr.toString("hex")}`);
  }
}

function expectMergeTreePipeline(inputBytes, needle) {
  const makeTree = compileStdinExcept(jsonMergeTreeModule, "makeMergedTree", 4096);
  const searchTree = compileStdinArgvExcept(jsonMergeTreeModule, "searchMergedTree", 8192, 8, 256);
  const makeResult = runWasmtimeWithInput(makeTree, "makeMergedTree", "merge-tree", inputBytes);
  if (makeResult.status !== 0) {
    throw new Error(outputText(makeResult).trim() || "makeMergedTree failed in Wasmtime");
  }
  const makeJson = JSON.parse((makeResult.stdout || Buffer.alloc(0)).toString("utf8"));
  if (makeJson.gc.allocs <= 0) {
    throw new Error("makeMergedTree: expected allocation count to increase");
  }
  if (makeJson.gc.releasesBefore !== 0 || makeJson.gc.freesBefore !== 0) {
    throw new Error("makeMergedTree: expected no releases before explicit release");
  }
  if (makeJson.gc.freesAfterFirst <= makeJson.gc.freesBefore) {
    throw new Error("makeMergedTree: expected first source tree to be freed");
  }
  if (makeJson.gc.freesAfterSecond <= makeJson.gc.freesAfterFirst) {
    throw new Error("makeMergedTree: expected second source tree to be freed");
  }
  if (makeJson.gc.releasesAfterSecond !== makeJson.gc.freesAfterSecond) {
    throw new Error("makeMergedTree: expected releases and frees to match for unshared source trees");
  }
  const searchResult = runWasmtimeWithInputAndArgs(
    searchTree,
    "searchMergedTree",
    `needle-${needle}`,
    makeResult.stdout || Buffer.alloc(0),
    [needle]
  );
  if (searchResult.status !== 0) {
    throw new Error(outputText(searchResult).trim() || "searchMergedTree failed in Wasmtime");
  }
  const searchJson = JSON.parse((searchResult.stdout || Buffer.alloc(0)).toString("utf8"));
  if (searchJson.found !== true) {
    throw new Error("searchMergedTree: expected successful search");
  }
}

function expectGcTreeRewrite(inputBytes) {
  const wasm = compileStdinExcept(jsonGcTreeRewriteModule, "transform", 1024);
  const result = runWasmtimeWithInput(wasm, "jsonGcTreeRewrite", "gc-tree-rewrite", inputBytes);
  if (result.status !== 0) {
    throw new Error(outputText(result).trim() || "jsonGcTreeRewrite failed in Wasmtime");
  }
  const stderr = result.stderr || Buffer.alloc(0);
  if (stderr.length !== 0) {
    throw new Error(`jsonGcTreeRewrite: expected empty stderr, got ${stderr.toString("hex")}`);
  }
  const json = JSON.parse((result.stdout || Buffer.alloc(0)).toString("utf8"));
  if (json.nodeCount !== 63 || json.height !== 6) {
    throw new Error("jsonGcTreeRewrite: expected a depth-six tree");
  }
  if (json.gc.allocsAfterInitial <= 0 || json.gc.freesBeforeRun !== 0) {
    throw new Error("jsonGcTreeRewrite: unexpected initial GC counters");
  }
  if (json.gc.freesAfterRounds <= json.gc.freesBeforeRun) {
    throw new Error("jsonGcTreeRewrite: expected old generations to be freed");
  }
  if (json.gc.freesAfterFinal <= json.gc.freesAfterRounds) {
    throw new Error("jsonGcTreeRewrite: expected final generation to be freed");
  }
  if (json.gc.releasesAfterFinal !== json.gc.freesAfterFinal) {
    throw new Error("jsonGcTreeRewrite: expected releases and frees to match");
  }

  const invalid = runWasmtimeWithInput(
    wasm,
    "jsonGcTreeRewrite",
    "gc-tree-rewrite-invalid",
    bytes('{"depth":9,"rounds":1,"salt":17,"search":12345}')
  );
  if (invalid.status !== 1) {
    throw new Error(outputText(invalid).trim() || "jsonGcTreeRewrite should reject oversized depth");
  }
  const expected = Buffer.from('{"error":1}');
  const actual = invalid.stderr || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`jsonGcTreeRewrite: expected error ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
}

function expectArgvExceptError(moduleName, entry, maxArgs, maxArgBytes, args, expectedBytes) {
  const wasm = compileArgvExcept(moduleName, entry, maxArgs, maxArgBytes);
  const result = run([wasmtime, "run", wasm, ...args], {
    stdio: ["ignore", "pipe", "pipe"],
    timeout: 10000,
  });
  if (result.status !== 1) {
    throw new Error(outputText(result).trim() || `${entry} should have exited with status 1`);
  }
  const expected = Buffer.from(expectedBytes);
  const actual = result.stderr || Buffer.alloc(0);
  if (Buffer.compare(actual, expected) !== 0) {
    throw new Error(`${entry}: expected stderr ${expected.toString("hex")}, got ${actual.toString("hex")}`);
  }
  const stdout = result.stdout || Buffer.alloc(0);
  if (stdout.length !== 0) {
    throw new Error(`${entry}: expected empty stdout, got ${stdout.toString("hex")}`);
  }
}

function expectArgvTrap(moduleName, entry, maxArgs, maxArgBytes, args) {
  const wasm = compileArgvExcept(moduleName, entry, maxArgs, maxArgBytes);
  const result = run([wasmtime, "run", wasm, ...args], {
    stdio: ["ignore", "pipe", "pipe"],
    timeout: 10000,
  });
  if (result.status === 0) {
    throw new Error(`${entry} succeeded but should have trapped`);
  }
}

function expectStdinTrap(moduleName, entry, maxInputBytes, inputBytes) {
  const wasm = compileStdin(moduleName, entry, maxInputBytes);
  const result = runWasmtimeWithInput(wasm, entry, "trap", inputBytes);
  if (result.status === 0) {
    throw new Error(`${entry} succeeded but should have trapped`);
  }
}

function expectReject(entry, message) {
  const out = path.join(outDir, `${entry}.reject.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi",
    "--module",
    correctnessModule,
    "--entry",
    `${correctnessModule}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status === 0) {
    throw new Error(`${entry} compiled but should have failed`);
  }
  if (!outputText(result).includes(message)) {
    throw new Error(`${entry}: expected rejection containing "${message}"`);
  }
}

function expectStdinReject(moduleName, entry, maxInputBytes, message) {
  const out = path.join(outDir, `${entry}.reject.stdin.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi-stdin",
    "--max-input-bytes",
    maxInputBytes.toString(),
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status === 0) {
    throw new Error(`${entry} compiled but should have failed`);
  }
  if (!outputText(result).includes(message)) {
    throw new Error(`${entry}: expected rejection containing "${message}"`);
  }
}

function expectStdinExceptReject(moduleName, entry, maxInputBytes, message) {
  const out = path.join(outDir, `${entry}.reject.stdin-except.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi-stdin-except",
    "--max-input-bytes",
    maxInputBytes.toString(),
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status === 0) {
    throw new Error(`${entry} compiled but should have failed`);
  }
  if (!outputText(result).includes(message)) {
    throw new Error(`${entry}: expected rejection containing "${message}"`);
  }
}

function expectArgvExceptReject(moduleName, entry, maxArgs, maxArgBytes, message) {
  const out = path.join(outDir, `${entry}.reject.argv-except.wasi.wasm`);
  const result = run([
    leanExe,
    "compile-wasi-argv-except",
    "--max-args",
    maxArgs.toString(),
    "--max-argv-bytes",
    maxArgBytes.toString(),
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${entry}`,
    "--out",
    out,
  ]);
  if (result.status === 0) {
    throw new Error(`${entry} compiled but should have failed`);
  }
  if (!outputText(result).includes(message)) {
    throw new Error(`${entry}: expected rejection containing "${message}"`);
  }
}

function main() {
  if (!fs.existsSync(wasmtime)) {
    throw new Error(`wasmtime not found: ${wasmtime}`);
  }
  fs.mkdirSync(outDir, { recursive: true });

  expectProgram("byteArrayStringConstReturn", [88, 89, 90]);
  expectProgram("byteArrayAppendReturn", [65, 66, 67]);
  expectProgram("byteArrayFoldByteArrayAccumulator", [1, 2]);
  expectProgram("idRunRangeForByteArrayOutput", [1, 1]);

  expectStdinProgram(correctnessModule, "byteArrayIdentityReturn", 8, [65, 66], [65, 66]);
  expectStdinProgram(byteArrayModule, "appendBang", 8, [65, 66], [65, 66, 33]);
  expectStdinProgram(byteArrayModule, "tailSlice", 8, [65, 66, 67], [66, 67]);
  expectStdinTrap(correctnessModule, "byteArrayIdentityReturn", 8, [65, 66, 67, 68, 69, 70, 71, 72, 73]);
  expectStdinExceptOk(correctnessModule, "byteArrayExceptBangOrError", 8, [65, 66], [65, 66, 33]);
  expectStdinExceptError(correctnessModule, "byteArrayExceptBangOrError", 8, [], [101, 109, 112, 116, 121]);
  expectStdinExceptOk(jsonGcdModule, "transform", 1024, bytes("[48,18,30]"), bytes('{"gcd":6}'));
  expectStdinExceptOk(jsonGcdModule, "transform", 1024, bytes(" [ 0 , 42 , 56 ] "), bytes('{"gcd":14}'));
  expectStdinExceptOk(jsonGcdModule, "transform", 1024, bytes("[17]"), bytes('{"gcd":17}'));
  expectStdinExceptError(jsonGcdModule, "transform", 1024, bytes("[]"), bytes('{"error":1}'));
  expectStdinExceptError(jsonGcdModule, "transform", 1024, bytes('[4,"x"]'), bytes('{"error":1}'));
  expectStdinExceptError(jsonGcdModule, "transform", 1024, bytes("[1,]"), bytes('{"error":1}'));
  expectArgvExceptOk(byteArrayModule, "argvFirstLast", 4, 1024, ["alpha", "omega"], [
    97, 108, 112, 104, 97, 58, 111, 109, 101, 103, 97,
  ]);
  expectArgvExceptError(byteArrayModule, "argvFirstLast", 4, 1024, [], [109, 105, 115, 115, 105, 110, 103]);
  expectArgvTrap(byteArrayModule, "argvFirstLast", 1, 1024, ["one", "two"]);
  expectTreePipeline(bytes("[1,6,4,100,33,5,5,20]"), "4", bytes('{"found":true}'));
  expectTreePipeline(bytes("[1,6,4,100,33,5,5,20]"), "7", bytes('{"found":false}'));
  expectMergeTreePipeline(bytes("[[1,6,4,100],[33,5,5,20]]"), "4");
  expectGcTreeRewrite(bytes('{"depth":6,"rounds":8,"salt":17,"search":12345}'));

  expectReject("byteArrayPushSize", "program entry must return ByteArray");
  expectReject("byteArrayBranchHelperReturn", "program entry must take no parameters");
  expectStdinReject(
    correctnessModule,
    "byteArrayStringConstReturn",
    8,
    "program stdin entry must have type ByteArray -> ByteArray"
  );
  expectStdinReject(
    correctnessModule,
    "byteArrayIdentityReturn",
    1048576,
    "max input bytes exceeds WASM memory capacity"
  );
  expectStdinExceptReject(
    correctnessModule,
    "byteArrayIdentityReturn",
    8,
    "program stdin-except entry must have type ByteArray -> Except ByteArray ByteArray"
  );
  expectArgvExceptReject(
    correctnessModule,
    "byteArrayIdentityReturn",
    4,
    1024,
    "program argv-except entry must have type Array ByteArray -> Except ByteArray ByteArray"
  );
  expectArgvExceptReject(
    byteArrayModule,
    "argvFirstLast",
    60000,
    60000,
    "max argv storage exceeds WASM memory capacity"
  );

  process.stdout.write("checked 22 WASI program cases, 2 traps, and 7 rejections\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
