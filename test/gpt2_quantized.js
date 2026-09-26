#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Models.Gpt2.Quantized.Grouped";
const namespace = "LeanExe.Models.Gpt2.Quantized";
const run = args => runChecked(args, { encoding: "utf8" }).stdout.trim();
const f32 = Math.fround;
const scratch = Buffer.alloc(4);
function bits(value) { scratch.writeFloatLE(value); return scratch.readUInt32LE(); }
function fromBits(value) { scratch.writeUInt32LE(value); return scratch.readFloatLE(); }
function floats(values) {
  const bytes = Buffer.alloc(values.length * 4);
  values.forEach((value, i) => bytes.writeFloatLE(value, i * 4));
  return bytes;
}
function quantize(value, scale) {
  const quotient = Math.min(127, Math.max(-127, f32(value / scale)));
  const lower = Math.floor(quotient), remainder = quotient - lower;
  return remainder < 0.5 ? lower : remainder > 0.5 ? lower + 1 : lower + (lower & 1);
}
function rowScale(values) {
  const maximum = Math.max(...values.map(Math.abs));
  return maximum === 0 ? 1 : Math.max(2 ** -126, f32(maximum / 127));
}

function main() {
  run(["lake", "build", "lean-wasm", moduleName]);
  const directory = fs.mkdtempSync("tmp/gpt2-quantized-");
  const modules = {};
  for (const entry of ["quantizeValue", "rowScale", "dot", "linearRows", "linearChecked", "linearGroupedRows"]) {
    modules[entry] = path.join(directory, `${entry}.wasm`);
    run([".lake/build/bin/lean-wasm", "compile", "--module", moduleName,
      "--entry", `${namespace}.${entry}`, "--out", modules[entry]]);
  }
  const expressions = [], expectedNative = [];
  const sourceBytes = bytes => `(ByteArray.mk #[${[...bytes].join(",")}])`;
  function source(expression, expected) { expressions.push(expression); expectedNative.push(expected); }
  let count = 0;
  for (const value of [-1000, -127, -126.5, -3.5, -2.5, -1.5, -0.5, -0, 0,
    0.5, 1.5, 2.5, 3.5, 126.5, 127, 1000, 2 ** -149, -(2 ** -149)]) {
    const scale = 1, expected = quantize(value, scale) & 255;
    assert.equal(host.callI64(modules.quantizeValue, "quantizeValue",
      [host.i64(bits(value)), host.i64(bits(scale))]), BigInt(expected));
    source(`(${namespace}.quantizeValue ${bits(value)} ${bits(scale)}).toNat`, expected);
    count++;
  }
  for (const values of [[0, -0], [2 ** -149, -(2 ** -149)], [1, -127],
    [fromBits(0x7f7fffff), -1]]) {
    const input = floats(values), expected = bits(rowScale(values));
    assert.equal(host.callI64(modules.rowScale, "rowScale",
      [host.byteArray(input), host.i64(0), host.i64(values.length)]), BigInt(expected));
    source(`(${namespace}.rowScale ${sourceBytes(input)} 0 ${values.length}).toNat`, expected);
    count++;
  }
  for (const [length, x, w] of [[0, 127, 127], [1, -127, 127],
    [3072, 127, 127], [3072, -127, 127], [3072, -127, -127]]) {
    const input = Buffer.alloc(length, x & 255), weights = Buffer.alloc(length, w & 255);
    const expected = (length * x * w) >>> 0;
    assert.equal(host.callI64(modules.dot, "dot", [host.byteArray(weights), host.byteArray(input),
      host.i64(0), host.i64(0), host.i64(length)]), BigInt(expected));
    source(`(${namespace}.dot ${sourceBytes(weights)} ${sourceBytes(input)} 0 0 ${length}).toNat`, expected);
    count++;
  }
  function checked(weights, input, dimensions, expectedStatus, expectedOutput) {
    const args = [host.byteArray(weights), host.byteArray(input), ...dimensions.map(host.i64)];
    const stats = host.callStats(modules.linearChecked, "linearChecked", "slots:3", args);
    const slots = stats.result.split(/\s+/).map(BigInt);
    assert.equal(slots[0], BigInt(expectedStatus));
    assert.equal(slots[2], BigInt(expectedOutput.length));
    assert.equal(stats.allocs - stats.frees, expectedStatus === 0 ? 3n : 2n,
      "only inputs and a successful result survive");
    const result = host.script(modules.linearChecked,
      [`bytes 0 ${weights.toString("hex")}`, `bytes 1 ${input.toString("hex")}`,
        "arg-ptr 0", `arg-u64 ${weights.length}`, "arg-ptr 1", `arg-u64 ${input.length}`,
        ...dimensions.map(value => `arg-u64 ${value}`)], "linearChecked", 3,
      ["read-memory result:1 result:2"]);
    assert.deepEqual(Buffer.from(result.memoryChunks[0].bytes), expectedOutput);
    const expression = `${namespace}.linearChecked ${sourceBytes(weights)} ${sourceBytes(input)} ` +
      dimensions.slice(0, -1).join(" ") + ` ${dimensions.at(-1) ? "true" : "false"}`;
    source(`(let r := ${expression}; (r.status.toNat, r.output.data.toList.map UInt8.toNat))`,
      [expectedStatus, [...expectedOutput]]);
    count++;
  }
  const weights = Buffer.concat([Buffer.from([127, 129, 2, 3, 4, 251]),
    floats([0.25, 0.5]), floats([1, -2])]);
  const values = [127, -127, 2, 0, 0, 0], input = floats(values);
  const dimensions = [0, 6, 14, 3, 2, 2, 1];
  const expected = floats([f32(f32(f32(32262) * 0.25) + 1),
    f32(f32(f32(-137) * 0.5) - 2), 1, -2]);
  checked(weights, input, dimensions, 0, expected);
  const direct = host.callStats(modules.linearRows, "linearRows", "bytes",
    [host.byteArray(weights), host.byteArray(input), ...dimensions.map(host.i64)]);
  assert.deepEqual(Buffer.from(direct.result, "hex"), expected);
  assert.equal(direct.allocs, 5n, "inputs, scales, quantized rows, and output");
  assert.equal(direct.frees, 2n, "release scales and quantized rows");
  checked(weights, input, [0, 6, 14, 3073, 2, 2, 1], 1, Buffer.alloc(0));
  checked(weights, input, [weights.length, 6, 14, 3, 2, 2, 1], 1, Buffer.alloc(0));
  const reserved = Buffer.from(weights); reserved[0] = 128;
  checked(reserved, input, dimensions, 2, Buffer.alloc(0));
  const invalidScale = Buffer.from(weights); invalidScale.writeUInt32LE(0, 6);
  checked(invalidScale, input, dimensions, 2, Buffer.alloc(0));
  const invalidInput = Buffer.from(input); invalidInput.writeUInt32LE(0x7fc00000, 0);
  checked(weights, invalidInput, dimensions, 3, Buffer.alloc(0));
  const overflowing = Buffer.from(weights); overflowing.writeUInt32LE(0x7f7fffff, 6);
  checked(overflowing, input, dimensions, 4, Buffer.alloc(0));
  for (const width of [64, 128]) {
    const coefficients = Buffer.from(Array.from({ length: 2 * width }, (_, i) => ((i % 13) - 6) & 255));
    const scales = [0.25, 0.5], biases = [1, -2];
    const groupedWeights = Buffer.concat([coefficients, floats(scales), floats(biases)]);
    const groupedInput = Array.from({ length: 2 * width }, (_, i) =>
      i >= width ? (i % 2 ? -(2 ** -149) : 2 ** -149) :
        i < 64 ? (i === 0 ? 127 : (i % 9) - 3.5) : f32(((i % 7) - 3) / 256));
    for (const withBias of [false, true]) {
      const outputs = [];
      for (let row = 0; row < 2; row++) {
        for (let column = 0; column < 2; column++) {
          let total = 0;
          for (let offset = 0; offset < width; offset += 64) {
            const group = groupedInput.slice(row * width + offset, row * width + offset + 64);
            const scale = rowScale(group);
            let accumulator = 0;
            for (let i = 0; i < 64; i++) {
              accumulator += quantize(group[i], scale) * coefficients.readInt8(column * width + offset + i);
            }
            total = f32(total + f32(accumulator * f32(scale * scales[column])));
          }
          outputs.push(withBias ? f32(total + biases[column]) : total);
        }
      }
      const dimensions = [0, 2 * width, 2 * width + 8, width, 2, 2, Number(withBias)];
      const stats = host.callStats(modules.linearGroupedRows, "linearGroupedRows", "bytes",
        [host.byteArray(groupedWeights), host.byteArray(floats(groupedInput)), ...dimensions.map(host.i64)]);
      const expected = floats(outputs);
      assert.deepEqual(Buffer.from(stats.result, "hex"), expected);
      assert.equal(stats.allocs, 5n);
      assert.equal(stats.frees, 2n);
      source(`(${namespace}.linearGroupedRows ${sourceBytes(groupedWeights)} ${sourceBytes(floats(groupedInput))} ` +
        `0 ${2 * width} ${2 * width + 8} ${width} 2 2 ${withBias}).data.toList.map UInt8.toNat`, [...expected]);
      count++;
    }
  }
  const native = path.join(directory, "Reference.lean");
  fs.writeFileSync(native, `import Lean\nimport ${moduleName}\n` +
    expressions.map(expression => `#eval IO.println (Lean.Json.compress (Lean.toJson (${expression})))\n`).join(""));
  assert.deepEqual(run(["lake", "env", "lean", native]).split(/\r?\n/).map(JSON.parse), expectedNative);
  process.stdout.write(`Checked ${count} quantized scalar, projection, rejection, and allocation cases in Lean and Wasmtime\n`);
}

try { main(); } catch (error) { console.error(error.stack); process.exitCode = 1; }
