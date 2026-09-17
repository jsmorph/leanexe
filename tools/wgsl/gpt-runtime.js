"use strict";

// Native implementation of the declared conversion/transfer boundary. Node's
// Wasm engine and the WebGPU implementation remain explicit runtime assumptions.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { instantiate, nativeDispatch } = require("./wasm-host");
const requireThat = (ok, message) => { if (!ok) throw new Error(message); };
const digest = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const unsigned = word => BigInt.asUintN(64, word);
const scratch = new DataView(new ArrayBuffer(8));
function decode64(word) { scratch.setBigUint64(0, unsigned(word), true); return scratch.getFloat64(0, true); }
function encode64(value) { scratch.setFloat64(0, value, true); return scratch.getBigUint64(0, true); }

function execute(checked, tokens, reference, label) {
  requireThat(Array.isArray(tokens) && tokens.length === 4 &&
    tokens.every(t => Number.isInteger(t) && t >= 0 && t < 256), "expected four byte tokens");
  requireThat(/^[a-z0-9-]+$/.test(label), "invalid evidence label");
  const report = { schemaVersion: 1, status: "error", tokens,
    hiddenSha256: digest(checked.hiddenBytes), shaderSha256: digest(checked.shader),
    bridgeSha256: digest(checked.hostBytes), finishSha256: digest(checked.finishBytes),
    weightsSha256: digest(checked.weightsBytes), profile: checked.metadata.profile,
    wasmRuntime: { node: process.version, v8: process.versions.v8 }, runtimeConformanceEstablished: false };
  const destination = path.join(checked.attempt, `gpt-${label}.json`);
  requireThat(!fs.existsSync(destination), "execution evidence already exists");
  try {
    requireThat(checked.metadata.profile.id === "leanexe-f32-rne-separate-v1",
      "this exact-reference execution requires the separate profile");
    requireThat(checked.weightsBytes.length === 2488 * 8, "wrong checkpoint size");
    const hidden = new WebAssembly.Instance(new WebAssembly.Module(checked.hiddenBytes), {});
    const { memory } = hidden.exports;
    requireThat(memory instanceof WebAssembly.Memory && typeof hidden.exports.hidden === "function", "missing hidden exports");
    // Explicit input state satisfying UInt64Array.At; no allocator call is used.
    const pointer = 256;
    requireThat(pointer + 8 + checked.weightsBytes.length <= memory.buffer.byteLength, "checkpoint does not fit initial memory");
    new DataView(memory.buffer).setBigUint64(pointer, 2488n, true);
    new Uint8Array(memory.buffer, pointer + 8, checked.weightsBytes.length).set(checked.weightsBytes);
    const before = Buffer.from(new Uint8Array(memory.buffer));
    const values = hidden.exports.hidden(BigInt(pointer), ...tokens.map(BigInt), 3n);
    requireThat(Array.isArray(values) && values.length === 4, "wrong hidden result shape");
    const hiddenWords = values.map(unsigned);
    requireThat(hiddenWords.every((word, i) => word.toString() === reference.hidden[i]), "hidden Wasm differs from pure Lean model");
    requireThat(Buffer.from(memory.buffer).equals(before), "hidden Wasm changed input memory");

    const bridge = instantiate(checked.hostBytes, checked.metadata, inputs =>
      nativeDispatch(checked, inputs, path.join(checked.attempt, `gpt-${label}-native.log`)));
    const bridgeMemory = bridge.instance.exports.memory;
    const a = 64, b = 128, c = b + 4 * 1024 + 64;
    const view = new DataView(bridgeMemory.buffer);
    hiddenWords.forEach((word, i) => view.setFloat32(a + 4 * i, decode64(word), true));
    for (let i = 0; i < 1024; i++) view.setFloat32(b + 4 * i, checked.weightsBytes.readDoubleLE(8 * (1184 + i)), true);
    const bridgeBefore = Buffer.from(new Uint8Array(bridgeMemory.buffer));
    requireThat(bridge.instance.exports.run(a, b, c) === 0 && bridge.calls === 1, "head dispatch failed");
    const bridgeAfter = Buffer.from(bridgeMemory.buffer);
    requireThat(bridgeAfter.subarray(0, c).equals(bridgeBefore.subarray(0, c)) &&
      bridgeAfter.subarray(c + 1024).equals(bridgeBefore.subarray(c + 1024)), "bridge changed memory outside output");

    const finish = new WebAssembly.Instance(new WebAssembly.Module(checked.finishBytes), {});
    requireThat(typeof finish.exports.finish === "function", "missing finish export");
    const logits = Array.from({ length: 256 }, (_, j) => {
      const promoted = encode64(view.getFloat32(c + 4 * j, true));
      const bias = checked.weightsBytes.readBigUInt64LE(8 * (2208 + j));
      return unsigned(finish.exports.finish(promoted, bias));
    });
    requireThat(Array.isArray(reference.logits) && reference.logits.length === 256 &&
      logits.every((word, j) => word.toString() === reference.logits[j]), "mixed logits differ from pure Lean model");
    requireThat(logits.every(word => Number.isFinite(decode64(word))), "nonfinite mixed logit");
    Object.assign(report, { status: "pass", hidden: hiddenWords.map(String), logits: logits.map(String),
      runtime: bridge.last.runtime, checkedElements: 256, hiddenMemoryPreserved: true,
      bridgeMemoryOutsideOutputPreserved: true, importedCalls: bridge.calls,
      reference: "pure Lean integer binary64 hidden and binary32 separate head with explicit conversions" });
    return report;
  } catch (error) {
    report.error = error.message;
    throw error;
  } finally {
    fs.writeFileSync(destination, JSON.stringify(report, null, 2) + "\n", { flag: "wx" });
  }
}
module.exports = { execute };
