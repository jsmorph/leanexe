"use strict";

// Foreign-runtime implementation of Project.WGSL.HostExecution.contract.
// This JavaScript, Node's Wasm engine and the native WebGPU stack are explicit
// conformance assumptions. The bundle gate verifies the actual artifacts.
const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");
const root = path.resolve(__dirname, "../..");
const requireThat = (condition, message) => { if (!condition) throw new Error(message); };

function nativeDispatch(checked, inputs, logPath) {
  const job = { wgsl: checked.shader.toString("utf8"), manifest: checked.metadata, inputs,
    backend: process.env.WGPU_BACKEND_TYPE || "Vulkan",
    adapter: process.env.LEANEXE_WGPU_ADAPTER || (process.platform === "darwin" ? "SwiftShader" : "llvmpipe") };
  return nativeJob(job, logPath);
}

function nativeJob(job, logPath) {
  const command = process.platform === "darwin" ? path.join(__dirname, "run-macos-cpu.sh") :
    (process.env.LEANEXE_WGPU_PYTHON || "python3");
  const args = process.platform === "darwin" ? ["--worker"] : [path.join(__dirname, "run.py"), "--worker"];
  const result = spawnSync(command, args, { cwd: root, env: process.env, encoding: "utf8", timeout: 45000,
    input: JSON.stringify(job), maxBuffer: 4 * 1024 * 1024 });
  fs.writeFileSync(logPath, (result.stdout || "") + (result.stderr || ""), { flag: "wx" });
  requireThat(!result.error && result.status === 0, `native WebGPU worker failed; see ${logPath}`);
  const response = JSON.parse(result.stdout);
  requireThat(!response.error, response.error);
  return response;
}

function instantiate(hostBytes, metadata, dispatch) {
  const { a, b, c } = metadata.buffers;
  const { rows, cols, inner } = metadata.dimensions;
  requireThat([a, b, c].every(v => Number.isSafeInteger(v.elements) && v.elements > 0 &&
    v.elements <= 16384 && v.bytes === 4 * v.elements) && rows * cols * inner <= 262144,
  "GEMM exceeds host resource caps");
  let instance;
  let calls = 0;
  let last;
  const invoke = (aOffset, bOffset, cOffset) => {
    const offsets = { a: aOffset >>> 0, b: bOffset >>> 0, c: cOffset >>> 0 };
    const memory = instance.exports.memory;
    const originalBuffer = memory.buffer;
    for (const name of ["a", "b", "c"]) {
      requireThat(offsets[name] % 4 === 0, `${name} offset must be four-byte aligned`);
      requireThat(offsets[name] + metadata.buffers[name].bytes <= originalBuffer.byteLength &&
        offsets[name] + metadata.buffers[name].bytes <= 2 ** 32, `${name} region is outside Wasm memory`);
    }
    const view = new DataView(originalBuffer);
    // Snapshot both inputs before any output write, including when regions alias.
    const inputs = Object.fromEntries(["a", "b"].map(name => [name,
      Array.from({ length: metadata.buffers[name].elements }, (_, i) => view.getUint32(offsets[name] + 4 * i, true))]));
    calls++;
    const response = dispatch(inputs);
    requireThat(memory.buffer === originalBuffer, "Wasm memory changed during dispatch");
    requireThat(Array.isArray(response.outputs) && response.outputs.length === c.elements &&
      response.outputs.every(word => Number.isInteger(word) && word >= 0 && word < 2 ** 32),
    "invalid native output buffer");
    // Validate the complete response before committing any output bytes.
    response.outputs.forEach((word, i) => view.setUint32(offsets.c + 4 * i, word, true));
    last = { offsets, inputs, outputs: response.outputs, runtime: response.runtime };
    return 0;
  };
  instance = new WebAssembly.Instance(new WebAssembly.Module(hostBytes), {
    "leanexe.webgpu": { gemm_f32: invoke },
  });
  requireThat(instance.exports.memory instanceof WebAssembly.Memory && typeof instance.exports.run === "function",
    "missing Wasm bridge exports");
  return { instance, get calls() { return calls; }, get last() { return last; } };
}

module.exports = { instantiate, nativeDispatch, nativeJob };
