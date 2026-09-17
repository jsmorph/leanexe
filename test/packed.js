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
  run([".venv-tiny-gpt2/bin/python", "training/gpt2/reference.py", "export-kernel"]);
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

function main() {
  assert.ok(process.argv.slice(2).every(arg => arg === "--gpt2-kernel"),
    "usage: packed.js [--gpt2-kernel]");
  run(["lake", "build", "lean-wasm", moduleName]);
  run(["tools/build-wasmtime-host.sh"]);
  fs.mkdirSync("tmp", { recursive: true });
  const output = fs.mkdtempSync(path.join("tmp", "packed-"));
  const modules = {};
  for (const entry of ["readWord", "makeWords", "shifted", "generateRead",
    "generateStats", "temporarySum", "generateSum"]) {
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
  for (const [input, offset] of [[Buffer.alloc(0), 0], [Buffer.alloc(3), 0],
    [bytes, bytes.length - 3], [bytes, (1n << 64n) - 1n]]) {
    const result = spawnResult([host.ensureHost(), "call", modules.readWord, "readWord", "i64",
      host.byteArray(input), host.i64(offset)], { encoding: "utf8" });
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /unreachable/);
  }
  for (const size of [0, 1, 17, 1024]) {
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
  const input = Buffer.alloc(12);
  [0, 1, 2].forEach((x, i) => input.writeFloatLE(x, i * 4));
  const shifted = Buffer.from(host.callBytes(modules.shifted, "shifted",
    [host.byteArray(input), host.i64(0x3f800000)]));
  assert.deepEqual([0, 1, 2].map(i => shifted.readFloatLE(i * 4)), [1, 2, 3]);
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
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
