#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { runChecked, spawnResult } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.Packed";
const compiler = process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm";
const run = args => runChecked(args, { encoding: "utf8" }).stdout.trim();

function testGpt2Kernel() {
  run(["uv", "run", "--color", "never", "--project", "training/gpt2", "training/gpt2/reference.py", "export-kernel"]);
  const kernelModule = "LeanExe.Models.Gpt2.Kernel";
  run(["lake", "build", kernelModule]);
  const directory = "build/gpt2-124m/kernel";
  const metadata = JSON.parse(fs.readFileSync(path.join(directory, "manifest.json")));
  const wasm = path.join(directory, "linear.wasm");
  run([compiler, "compile", "--module", kernelModule, "--entry", "LeanExe.Models.Gpt2.linear",
    "--out", wasm]);
  const started = process.hrtime.bigint();
  const result = host.callStats(wasm, "linear", "bytes", [
    `bytes-file:${directory}/weights.bin`, `bytes-file:${directory}/input.bin`,
    ...[metadata.weight_offset, metadata.bias_offset, metadata.input_width, metadata.output_width]
      .map(host.i64),
  ]);
  const seconds = Number(process.hrtime.bigint() - started) / 1e9;
  const actual = Buffer.from(result.result, "hex");
  const serial = fs.readFileSync(path.join(directory, "serial.bin"));
  const pytorch = fs.readFileSync(path.join(directory, "pytorch.bin"));
  assert.equal(actual.length, metadata.output_width * 4);
  assert.deepEqual(actual, serial, "GPT-2 linear output matches serial PyTorch FP32 bit-for-bit");
  let maximum = 0;
  for (let offset = 0; offset < actual.length; offset += 4)
    maximum = Math.max(maximum, Math.abs(actual.readFloatLE(offset) - pytorch.readFloatLE(offset)));
  assert.equal(result.allocs, 3n, "two host inputs and one packed output");
  const record = {
    checkpoint_sha256: metadata.checkpoint_sha256, tensor: metadata.tensor,
    input_width: metadata.input_width, output_width: metadata.output_width,
    wasm_sha256: crypto.createHash("sha256").update(fs.readFileSync(wasm)).digest("hex"),
    exact_serial_fp32: true, pytorch_max_abs_difference: maximum,
    host_call_seconds: seconds, allocations: Number(result.allocs),
  };
  fs.writeFileSync(path.join(directory, "wasm-test.json"), JSON.stringify(record, null, 2) + "\n");
  process.stdout.write(JSON.stringify(record) + "\n");
}

function testGpt2Block() {
  run(["uv", "run", "--color", "never", "--project", "training/gpt2", "training/gpt2/reference.py", "export-block"]);
  const module = "LeanExe.Models.Gpt2.Block";
  run(["lake", "build", module]);
  const directory = "build/gpt2-124m/block";
  const metadata = JSON.parse(fs.readFileSync(path.join(directory, "manifest.json")));
  const offsets = metadata.offsets_words;
  const files = {};
  const reports = [];
  const compiled = new Map();
  const file = name => `bytes-file:${files[name] || `${directory}/${name}.bin`}`;
  function evaluate(stage, entry, args) {
    if (!compiled.has(entry)) {
      const wasm = path.join(directory, `${entry}.wasm`);
      run([compiler, "compile", "--module", module, "--entry", `LeanExe.Models.Gpt2.${entry}`,
        "--out", wasm]);
      compiled.set(entry, wasm);
    }
    const started = process.hrtime.bigint();
    const stats = host.callStats(compiled.get(entry), entry, "bytes", args);
    const seconds = Number(process.hrtime.bigint() - started) / 1e9;
    const actual = Buffer.from(stats.result, "hex");
    const expected = fs.readFileSync(path.join(directory, `${stage === "block" ? "output" : stage}.bin`));
    assert.equal(actual.length, expected.length, stage);
    let maximum = 0;
    for (let offset = 0; offset < actual.length; offset += 4) {
      const x = actual.readFloatLE(offset), y = expected.readFloatLE(offset);
      const difference = Math.abs(x - y);
      assert.ok(Number.isFinite(x) && difference <= 1e-4 + 2e-5 * Math.abs(y),
        `${stage}[${offset / 4}]: WASM ${x}, PyTorch ${y}, difference ${difference}`);
      maximum = Math.max(maximum, difference);
    }
    files[stage] = path.join(directory, `${stage}.wasm-output.bin`);
    fs.writeFileSync(files[stage], actual);
    const report = { stage, max_abs_difference: maximum, host_call_seconds: seconds,
      allocations: Number(stats.allocs), frees: Number(stats.frees) };
    reports.push(report);
    process.stdout.write(JSON.stringify(report) + "\n");
    return stats;
  }
  const dimensions = (...values) => values.map(host.i64);
  const norm = (stage, input, name) => evaluate(stage, "layerNorm",
    [file("weights"), file(input), ...dimensions(offsets[`${name}.weight`], offsets[`${name}.bias`], metadata.rows)]);
  const linear = (stage, input, name, inWidth, outWidth) => evaluate(stage, "linearRows",
    [file("weights"), file(input), ...dimensions(offsets[`${name}.weight`], offsets[`${name}.bias`],
      inWidth, outWidth, metadata.rows)]);
  norm("normalized", "input", "ln_1");
  linear("qkv", "normalized", "attn.c_attn", 768, 2304);
  evaluate("mixed", "attention", [file("qkv"), host.i64(metadata.rows)]);
  linear("projected", "mixed", "attn.c_proj", 768, 768);
  evaluate("residual", "addRows", [file("input"), file("projected")]);
  norm("normalized2", "residual", "ln_2");
  linear("expanded", "normalized2", "mlp.c_fc", 768, 3072);
  evaluate("activated", "activate", [file("expanded")]);
  linear("projected2", "activated", "mlp.c_proj", 3072, 768);
  evaluate("output", "addRows", [file("residual"), file("projected2")]);
  const stats = evaluate("block", "transformerBlock", [file("weights"), file("input"),
    host.i64(0), host.i64(metadata.rows)]);
  assert.deepEqual(fs.readFileSync(files.block), fs.readFileSync(files.output),
    "composed block and separately called WASM stages match bit-for-bit");
  assert.equal(stats.allocs - stats.frees, 3n, "two input allocations and one output remain");
  const record = { checkpoint_sha256: metadata.checkpoint_sha256, rows: metadata.rows, reports };
  fs.writeFileSync(path.join(directory, "wasm-test.json"), JSON.stringify(record, null, 2) + "\n");
}

function testGpt2Inference() {
  run(["uv", "run", "--color", "never", "--project", "training/gpt2", "training/gpt2/reference.py", "export-model"]);
  const module = "LeanExe.Models.Gpt2.Inference";
  run(["lake", "build", module]);
  const directory = "build/gpt2-124m/inference";
  const metadata = JSON.parse(fs.readFileSync(path.join(directory, "manifest.json")));
  const wasm = path.join(directory, "infer.wasm");
  run([compiler, "compile", "--module", module, "--entry", "LeanExe.Models.Gpt2.infer", "--out", wasm]);
  const started = process.hrtime.bigint();
  const stats = host.callStats(wasm, "infer", "bytes",
    [`bytes-file:${directory}/weights.bin`, `bytes-file:${directory}/tokens.bin`]);
  const seconds = Number(process.hrtime.bigint() - started) / 1e9;
  const actual = Buffer.from(stats.result, "hex");
  const expected = fs.readFileSync(path.join(directory, "pytorch.bin"));
  assert.equal(actual.length, 50257 * 4);
  let maximum = 0, squared = 0, argmax = 0;
  for (let index = 0; index < 50257; index++) {
    const x = actual.readFloatLE(index * 4), y = expected.readFloatLE(index * 4);
    const difference = Math.abs(x - y);
    assert.ok(Number.isFinite(x) && difference <= 0.002 + 1e-4 * Math.abs(y),
      `logit ${index}: WASM ${x}, PyTorch ${y}, difference ${difference}`);
    maximum = Math.max(maximum, difference);
    squared += difference * difference;
    if (x > actual.readFloatLE(argmax * 4)) argmax = index;
  }
  assert.equal(argmax, metadata.argmax);
  const record = {
    checkpoint_sha256: metadata.checkpoint_sha256, parameters: metadata.parameters,
    tokens: metadata.tokens, argmax, argmax_text: metadata.argmax_text,
    max_abs_difference: maximum, rms_difference: Math.sqrt(squared / 50257),
    host_call_seconds: seconds, allocations: Number(stats.allocs), frees: Number(stats.frees),
    wasm_sha256: crypto.createHash("sha256").update(fs.readFileSync(wasm)).digest("hex"),
  };
  fs.writeFileSync(path.join(directory, "wasm-test.json"), JSON.stringify(record, null, 2) + "\n");
  fs.writeFileSync(path.join(directory, "wasm-logits.bin"), actual);
  process.stdout.write(JSON.stringify(record) + "\n");
  assert.equal(stats.allocs - stats.frees, 3n, "weights, tokens, and logits remain allocated");
}

function testGpt2Completions() {
  const records = [];
  for (const [text, count, seed, topK] of [
    ["Once upon a time, in a small village", 64, 42, 40],
    ["The purpose of science is", 32, 7, 40],
    ["The capital of France is", 16, 42, 1],
  ]) {
    const record = JSON.parse(run(["tools/gpt2", "--text", text, "--generate", String(count),
      "--seed", String(seed), "--top-k", String(topK), "--json"]));
    assert.equal(record.kv_cache, true);
    assert.equal(record.allocations - record.frees, 2);
    if (records.length === 0) {
      const original = JSON.parse(fs.readFileSync("data/gpt2-124m/wasm-completion-uncached.json"));
      assert.deepEqual(record.generated_tokens.slice(0, 16), original.generated_tokens,
        "cached sampling preserves the first full-prefix completion");
    }
    if (topK === 1) {
      const reference = JSON.parse(run(["tools/gpt2-pytorch",
        "--text", text, "--generate", String(count), "--top-k", "1", "--json"]));
      assert.deepEqual(record.generated_tokens, reference.generated_tokens, "greedy WASM and PyTorch text match");
      record.pytorch_greedy_tokens_exact = true;
    }
    records.push(record);
    fs.writeFileSync("build/gpt2-124m/wasm-completions.json", JSON.stringify(records, null, 2) + "\n");
    process.stdout.write(JSON.stringify(record) + "\n");
  }
}

function main() {
  assert.ok(process.argv.slice(2).every(arg => ["--gpt2-kernel", "--gpt2-block", "--gpt2-inference", "--gpt2-cached", "--gpt2-completions"].includes(arg)),
    "usage: packed.js [--gpt2-kernel] [--gpt2-block] [--gpt2-inference] [--gpt2-cached] [--gpt2-completions]");
  run(["lake", "build", "lean-wasm", moduleName]);
  run(["tools/build-wasmtime-host.sh"]);
  fs.mkdirSync("tmp", { recursive: true });
  const output = fs.mkdtempSync(path.join("tmp", "packed-"));
  const modules = {};
  for (const entry of ["readWord", "makeWords", "makeBytes", "shifted", "generateRead",
    "generateStats", "temporarySum", "generateSum", "generatedWithCall",
    "repeatedOwnedSum", "repeatedBorrowedSum", "repeatedPairSum", "publicPair"]) {
    modules[entry] = path.join(output, `${entry}.wasm`);
    run([compiler, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`,
      "--out", modules[entry]]);
  }
  const nativeExpressions = [];
  const expectedNative = [];
  const sourceBytes = bytes => `(ByteArray.mk #[${[...bytes].join(",")}])`;
  const bytes = Buffer.from("0123456789abcdef01020304", "hex");
  for (const offset of [0, 1, 4, bytes.length - 4]) {
    const expected = bytes.readUInt32LE(offset);
    assert.equal(host.callI64(modules.readWord, "readWord",
      [host.byteArray(bytes), host.i64(offset)]), BigInt(expected));
    nativeExpressions.push(`(${moduleName}.readWord ${sourceBytes(bytes)} ${offset}).toNat`);
    expectedNative.push(expected);
  }
  const file = path.join(output, "packed input.bin");
  fs.writeFileSync(file, bytes);
  assert.equal(host.callI64(modules.readWord, "readWord", [`bytes-file:${file}`, host.i64(1)]),
    BigInt(bytes.readUInt32LE(1)));
  const session = runChecked([host.ensureHost(), "session", modules.readWord], {
    encoding: "utf8", input: [
      `bytes-file 0 ${file}`,
      "arg-ptr 0", `arg-u64 ${bytes.length}`, "arg-u64 0", "call readWord 1",
      "arg-ptr 0", `arg-u64 ${bytes.length}`, "arg-u64 1", "call readWord 1",
      "arg-ptr 0", "call release 0", "stats", "done", "",
    ].join("\n"),
  }).stdout.trim().split("\n");
  assert.deepEqual(session, [`results ${bytes.readUInt32LE(0)}`, `results ${bytes.readUInt32LE(1)}`,
    "results", "stats 1 0 1 1"]);
  for (const [input, offset] of [[Buffer.alloc(0), 0], [Buffer.alloc(3), 0],
    [bytes, bytes.length - 3], [bytes, (1n << 64n) - 1n]]) {
    const result = spawnResult([host.ensureHost(), "call", modules.readWord, "readWord", "i64",
      host.byteArray(input), host.i64(offset)], { encoding: "utf8" });
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /unreachable/);
  }
  for (const size of [0, 1, 17, 1024]) {
    const byteExpected = Buffer.from(Array.from({ length: size }, (_, i) => (240 + i) & 255));
    const byteStats = host.callStats(modules.makeBytes, "makeBytes", "bytes",
      [host.i64(size), host.i64(240)]);
    assert.deepEqual(Buffer.from(byteStats.result, "hex"), byteExpected);
    assert.equal(byteStats.allocs, 1n, `one allocation for ${size} bytes`);
    nativeExpressions.push(`(${moduleName}.makeBytes ${size} 240).data.toList.map UInt8.toNat`);
    expectedNative.push([...byteExpected]);
    const offset = 0xfffffff0;
    const expected = Buffer.alloc(size * 4);
    for (let i = 0; i < size; i++) expected.writeUInt32LE((offset + i) >>> 0, i * 4);
    const stats = host.callStats(modules.makeWords, "makeWords", "bytes",
      [host.i64(size), host.i64(offset)]);
    assert.deepEqual(Buffer.from(stats.result, "hex"), expected);
    assert.equal(stats.allocs, 1n, `one allocation for ${size} words`);
    nativeExpressions.push(`(${moduleName}.makeWords ${size} ${offset}).data.toList.map UInt8.toNat`);
    expectedNative.push([...expected]);
    assert.equal(host.callI64(modules.generateStats, "generateStats", [host.i64(size)]),
      BigInt(size * 4000 + 1));
  }
  const generated = host.callBytes(modules.generateSum, "generateSum", [host.i64(12), host.i64(7)]);
  const sums = Buffer.alloc(48);
  for (let i = 0; i < 12; i++) sums.writeUInt32LE(7 + i * (i - 1) / 2, i * 4);
  assert.deepEqual(Buffer.from(generated), sums);
  nativeExpressions.push(`(${moduleName}.generateSum 12 7).data.toList.map UInt8.toNat`);
  expectedNative.push([...sums]);
  const temporary = host.callStats(modules.temporarySum, "temporarySum", "i64", [host.i64(16)]);
  assert.equal(temporary.result, "49");
  assert.equal(temporary.allocs, 1n);
  assert.equal(temporary.frees, 1n);
  for (const count of [0, 1, 4]) {
    const loop = host.callStats(modules.repeatedOwnedSum, "repeatedOwnedSum", "i64", [host.i64(count)]);
    assert.equal(loop.result, String(17 + count));
    assert.equal(loop.allocs, BigInt(count + 1));
    assert.equal(loop.frees, loop.allocs, "release the helper's final owned loop result");
    nativeExpressions.push(`(${moduleName}.repeatedOwnedSum ${count}).toNat`);
    expectedNative.push(17 + count);
    const pair = host.callStats(modules.repeatedPairSum, "repeatedPairSum", "i64",
      [host.byteArray(Buffer.from([3, 0, 0, 0])), host.i64(count)]);
    const pairSum = count === 0 ? 20 : 34 + 2 * count;
    assert.equal(pair.result, String(pairSum));
    assert.equal(pair.allocs, BigInt(3 + 3 * count), "evaluate both loop results together once");
    assert.equal(pair.frees, pair.allocs - 1n, "release both arrays and preserve the borrowed input");
    nativeExpressions.push(`(${moduleName}.repeatedPairSum (ByteArray.mk #[3, 0, 0, 0]) ${count}).toNat`);
    expectedNative.push(pairSum);
  }
  const borrowed = host.callStats(modules.repeatedBorrowedSum, "repeatedBorrowedSum", "i64",
    [host.byteArray(Buffer.from([7, 0, 0, 0])), host.i64(0)]);
  assert.equal(borrowed.result, "7");
  assert.equal(borrowed.allocs, 1n);
  assert.equal(borrowed.frees, 0n, "a zero-iteration borrowed loop result belongs to the caller");
  const pairStats = host.callStats(modules.publicPair, "publicPair", "slots:4");
  assert.equal(pairStats.allocs, 10n, "construct each public result field once");
  assert.equal(pairStats.frees, 8n, "preserve both public result owners");
  const pairValues = host.script(modules.publicPair, [], "publicPair", 4,
    ["read-memory result:0 result:1", "read-memory result:2 result:3"]);
  assert.deepEqual(pairValues.memoryChunks.map(chunk => [...Buffer.from(chunk.bytes)]),
    [[19, 0, 0, 0], [4, 0, 0, 0, 19, 0, 0, 0, 20, 0, 0, 0]]);
  for (const [index, size] of [[0, 4], [2, 12]])
    run([host.ensureHost(), "release-reuse", modules.publicPair, "publicPair", "4", String(index), String(size)]);
  const input = Buffer.alloc(12);
  [0, 1, 2].forEach((x, i) => input.writeFloatLE(x, i * 4));
  const shifted = Buffer.from(host.callBytes(modules.shifted, "shifted",
    [host.byteArray(input), host.i64(0x3f800000)]));
  assert.deepEqual([0, 1, 2].map(i => shifted.readFloatLE(i * 4)), [1, 2, 3]);
  const repeatedInput = Buffer.from([7, 0, 0, 0]);
  const repeated = Buffer.from(host.callBytes(modules.generatedWithCall, "generatedWithCall",
    [host.i64(3), host.byteArray(repeatedInput)]));
  assert.deepEqual([0, 1, 2].map(i => repeated.readUInt32LE(i * 4)), [0, 7, 14]);
  nativeExpressions.push(`(${moduleName}.generatedWithCall 3 ${sourceBytes(repeatedInput)}).data.toList.map UInt8.toNat`);
  expectedNative.push([...repeated]);
  assert.equal(host.callBytes(modules.generateRead, "generateRead",
    [host.i64(0), host.byteArray(Buffer.alloc(0))]).length, 0);
  const overflows = spawnResult([host.ensureHost(), "call", modules.makeWords, "makeWords", "bytes",
    host.i64(1n << 62n), host.i64(0)], { encoding: "utf8" });
  assert.notEqual(overflows.status, 0);
  assert.match(overflows.stderr, /unreachable/);
  const native = path.join(output, "Reference.lean");
  fs.writeFileSync(native, `import Lean\nimport ${moduleName}\n` +
    nativeExpressions.map(expression => `#eval IO.println (Lean.Json.compress (Lean.toJson (${expression})))\n`).join(""));
  assert.deepEqual(run(["lake", "env", "lean", native]).split(/\r?\n/).map(JSON.parse), expectedNative);
  process.stdout.write("Checked packed reads, unaligned offsets, bounds traps, binary files, one-allocation generation, loops, FP32 mapping, and temporary release\n");
  if (process.argv.includes("--gpt2-kernel")) testGpt2Kernel();
  if (process.argv.includes("--gpt2-block")) testGpt2Block();
  if (process.argv.includes("--gpt2-inference")) testGpt2Inference();
  if (process.argv.includes("--gpt2-cached"))
    runChecked(["uv", "run", "--color", "never", "--project", "training/gpt2", "training/gpt2/test_wasm.py"],
      { stdio: "inherit", timeout: 300000 });
  if (process.argv.includes("--gpt2-completions")) testGpt2Completions();
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
