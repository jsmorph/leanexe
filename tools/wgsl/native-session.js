"use strict";

// The Wasm import is synchronous. A Node worker owns the asynchronous native
// process; a bounded shared response lets the importing thread wait for complete
// readback without changing the proved Wasm ABI.
const path = require("node:path");
const { Worker } = require("node:worker_threads");
const requireThat = (ok, message) => { if (!ok) throw new Error(message); };
const CAPACITY = 1024 * 1024;

class NativeSession {
  constructor(checked, weights, log) {
    requireThat(Array.isArray(weights) && weights.length === checked.metadata.buffers.b.elements &&
      weights.every(word => Number.isInteger(word) && word >= 0 && word < 2 ** 32), "invalid resident weights");
    this.weights = weights.slice();
    this.control = new Int32Array(new SharedArrayBuffer(8));
    this.response = new Uint8Array(new SharedArrayBuffer(CAPACITY));
    this.closed = false;
    this.worker = new Worker(path.join(__dirname, "native-session-worker.js"), { workerData: {
      control: this.control.buffer, response: this.response.buffer, log,
      job: { wgsl: checked.shader.toString("utf8"), manifest: checked.metadata,
        inputs: { a: new Array(checked.metadata.buffers.a.elements).fill(0), b: this.weights },
        backend: process.env.WGPU_BACKEND_TYPE || "Vulkan",
        adapter: process.env.LEANEXE_WGPU_ADAPTER || (process.platform === "darwin" ? "SwiftShader" : "llvmpipe") },
    } });
    // Worker errors are also reported through the bounded response channel.
    this.worker.on("error", error => { this.workerError = error; });
  }

  request(message) {
    requireThat(!this.closed && !this.workerError, this.workerError?.message || "native session is closed");
    Atomics.store(this.control, 0, 0);
    this.worker.postMessage(message);
    const deadline = Date.now() + 45000;
    while (Atomics.load(this.control, 0) === 0) {
      const remaining = deadline - Date.now();
      requireThat(remaining > 0, "native session timed out waiting for readback");
      Atomics.wait(this.control, 0, 0, remaining);
    }
    const length = Atomics.load(this.control, 1);
    requireThat(length > 0 && length <= CAPACITY, "invalid native response length");
    const result = JSON.parse(Buffer.from(this.response.subarray(0, length)).toString("utf8"));
    requireThat(!result.error, result.error);
    return result;
  }

  dispatch(inputs) {
    requireThat(Array.isArray(inputs.b) && inputs.b.length === this.weights.length &&
      inputs.b.every((word, i) => word === this.weights[i]), "resident weights differ from the Wasm input snapshot");
    return this.request({ type: "dispatch", a: inputs.a });
  }

  async close() {
    if (this.closed) return;
    try { this.request({ type: "close" }); }
    finally {
      this.closed = true;
      await this.worker.terminate();
    }
  }
}

module.exports = { NativeSession };
