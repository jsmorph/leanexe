// Browser host bindings only. Transformer arithmetic, conversions, bias addition
// and greedy selection are executed by Wasm/WGSL artifacts, never by this file.
const A = 24576, B = 24640, C = 28736, LOGITS = 29760;
const requireThat = (ok, message) => { if (!ok) throw Error(message); };
const hex = bytes => Array.from(new Uint8Array(bytes), x => x.toString(16).padStart(2, "0")).join("");

export class ArtifactRunner {
  static async load() {
    requireThat(globalThis.isSecureContext && navigator.gpu,
      "WebGPU is unavailable here. Open this page on localhost or HTTPS in a WebGPU-enabled browser.");
    const response = await fetch("manifest.json", { cache: "no-store" });
    requireThat(response.ok, "Cannot load the artifact manifest");
    const manifest = await response.json();
    requireThat(manifest.schemaVersion === 1 && manifest.contextBytes === 128, "Unsupported demo bundle");
    async function artifact(name) {
      const response = await fetch(name, { cache: "no-store" });
      requireThat(response.ok, `Cannot load ${name}`);
      const bytes = await response.arrayBuffer();
      requireThat(hex(await crypto.subtle.digest("SHA-256", bytes)) === manifest.sha256[name],
        `${name} differs from the artifact manifest`);
      return bytes;
    }
    const [hiddenBytes, transferBytes, finishBytes, shaderBytes, weights] = await Promise.all(
      ["hidden.wasm", "transfer.wasm", "finish.wasm", "kernel.wgsl", "weights.bin"].map(artifact));
    requireThat(weights.byteLength === 23872, "Expected 2,984 binary64 weights");
    const { instance: hidden } = await WebAssembly.instantiate(hiddenBytes, {});
    const { instance: finish } = await WebAssembly.instantiate(finishBytes, {});
    const { instance: transfer } = await WebAssembly.instantiate(transferBytes, { finish: finish.exports });
    const adapter = await navigator.gpu.requestAdapter();
    requireThat(adapter, "No WebGPU adapter is available. Enable WebGPU or use another browser.");
    const device = await adapter.requestDevice();
    try {
      device.pushErrorScope("validation");
      const shader = device.createShaderModule({ code: new TextDecoder().decode(shaderBytes) });
      const pipeline = await device.createComputePipelineAsync({ layout: "auto", compute: { module: shader, entryPoint: "gemm_f32" } });
      const a = device.createBuffer({ size: 16, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
      const b = device.createBuffer({ size: 4096, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
      const c = device.createBuffer({ size: 1024, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC });
      const read = device.createBuffer({ size: 1024, usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST });
      const group = device.createBindGroup({ layout: pipeline.getBindGroupLayout(0), entries: [
        { binding: 0, resource: { buffer: a } }, { binding: 1, resource: { buffer: b } },
        { binding: 2, resource: { buffer: c } },
      ] });
      const error = await device.popErrorScope();
      requireThat(!error, error?.message);
      const runner = Object.assign(new ArtifactRunner(), { manifest, artifact, hidden: hidden.exports,
        transfer: transfer.exports, device, pipeline, a, b, c, read, group,
        originalWeights: new Uint8Array(weights), dispatches: 0, busy: false, failure: null,
        adapterInfo: adapter.info ? `${adapter.info.vendor} ${adapter.info.architecture} ${adapter.info.description}`.trim() : "Browser WebGPU" });
      device.lost.then(info => { runner.failure = Error(`WebGPU device lost: ${info.message}`); });
      device.addEventListener("uncapturederror", event => { runner.failure = Error(event.error.message); });
      runner.setWeights(runner.originalWeights);
      return runner;
    } catch (error) { device.destroy(); throw error; }
  }

  setWeights(bytes) {
    requireThat(!this.busy && bytes.byteLength === 23872, "Invalid weight transfer");
    this.weights = Uint8Array.from(bytes);
    new Uint8Array(this.transfer.memory.buffer, 0, bytes.byteLength).set(bytes);
    this.transfer.weights();
    this.device.queue.writeBuffer(this.b, 0, this.transfer.memory.buffer, B, 4096);
  }

  // Construct the compiler's Array UInt64 ABI. This changes representation only.
  array(bytes, tokenBytes) {
    const length = tokenBytes ? bytes.length : bytes.length / 8;
    const pointer = Number(this.hidden.alloc(BigInt(8 + 8 * length)));
    const buffer = this.hidden.memory.buffer;
    requireThat(Number.isSafeInteger(pointer) && pointer >= 0 && pointer + 8 + 8 * length <= buffer.byteLength,
      "Wasm input allocation is outside memory");
    const view = new DataView(buffer);
    view.setBigUint64(pointer, BigInt(length), true);
    if (tokenBytes) bytes.forEach((token, i) => view.setBigUint64(pointer + 8 + 8 * i, BigInt(token), true));
    else new Uint8Array(buffer, pointer + 8, bytes.length).set(bytes);
    return BigInt(pointer);
  }

  async step(tokens) {
    requireThat(!this.busy, "An inference step is already running");
    requireThat(tokens instanceof Uint8Array && tokens.length >= 1 && tokens.length <= 128,
      "Expected 1–128 input bytes");
    if (this.failure) throw this.failure;
    this.busy = true;
    try {
      this.hidden.reset();
      const weights = this.array(this.weights, false), context = this.array(tokens, true);
      const hidden = this.hidden.hidden(weights, context);
      requireThat(Array.isArray(hidden) && hidden.length === 4, "Invalid transformer result");
      this.transfer.prepare(...hidden);
      this.device.queue.writeBuffer(this.a, 0, this.transfer.memory.buffer, A, 16);
      const encoder = this.device.createCommandEncoder();
      const pass = encoder.beginComputePass();
      pass.setPipeline(this.pipeline); pass.setBindGroup(0, this.group); pass.dispatchWorkgroups(32, 1, 1); pass.end();
      encoder.copyBufferToBuffer(this.c, 0, this.read, 0, 1024);
      this.device.queue.submit([encoder.finish()]);
      await this.read.mapAsync(GPUMapMode.READ);
      try { new Uint8Array(this.transfer.memory.buffer, C, 1024).set(new Uint8Array(this.read.getMappedRange())); }
      finally { this.read.unmap(); }
      if (this.failure) throw this.failure;
      const token = this.transfer.finish();
      requireThat(Number.isInteger(token) && token >= 0 && token < 256, "Invalid predicted byte");
      this.dispatches++;
      const view = new DataView(this.transfer.memory.buffer);
      return { token, hidden: hidden.map(word => BigInt.asUintN(64, word).toString()),
        headWords: Array.from({ length: 256 }, (_, i) => view.getUint32(C + 4 * i, true).toString()),
        logits: Array.from({ length: 256 }, (_, i) => view.getBigUint64(LOGITS + 8 * i, true).toString()) };
    } finally { this.busy = false; }
  }

  async compare(notify) {
    const references = JSON.parse(new TextDecoder().decode(await this.artifact("reference.json")));
    const results = [];
    try {
      for (const reference of references) {
        const bytes = new Uint8Array(23872), view = new DataView(bytes.buffer);
        reference.preparedWeights.forEach((word, i) => view.setBigUint64(8 * i, BigInt(word), true));
        this.setWeights(bytes);
        const actual = await this.step(Uint8Array.from(reference.tokens));
        const differences = Object.fromEntries(["hidden", "headWords", "logits"].map(field =>
          [field, actual[field].filter((word, i) => word !== reference[field][i]).length]));
        const result = { name: reference.name, ...differences };
        results.push(result); notify(result);
        requireThat(differences.hidden === 0, `Generated transformer differs from Lean in ${reference.name}`);
      }
      return results;
    } finally { this.setWeights(this.originalWeights); }
  }

  destroy() { this.device.destroy(); }
}
