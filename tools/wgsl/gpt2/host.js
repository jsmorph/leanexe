// Browser bindings only: file validation, byte transfer, and execution schedule.
// Model arithmetic, UTF-8/BPE tokenization, and sampling run in Wasm/WGSL.
const F64 = 160000000, F32 = 161000000, EMPTY = new Uint8Array();
const need = (ok, text) => { if (!ok) throw Error(text); };
const hex = buffer => Array.from(new Uint8Array(buffer), b => b.toString(16).padStart(2, "0")).join("");
const words = values => {
  const bytes = new Uint8Array(values.length * 8), view = new DataView(bytes.buffer);
  values.forEach((v, i) => view.setBigUint64(i * 8, BigInt(v), true));
  return bytes;
};
const word = (bytes, index) => new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength).getBigUint64(index * 8, true);

class Wasm {
  constructor(exports) { this.w = exports; }
  array(bytes) {
    need(bytes.byteLength % 8 === 0, "Invalid Wasm array bytes");
    const pointer = Number(this.w.alloc(BigInt(8 + bytes.byteLength)));
    const memory = this.w.memory.buffer;
    need(pointer >= 0 && pointer + 8 + bytes.byteLength <= memory.byteLength, "Invalid Wasm allocation");
    new DataView(memory).setBigUint64(pointer, BigInt(bytes.byteLength / 8), true);
    new Uint8Array(memory, pointer + 8, bytes.byteLength).set(bytes);
    return BigInt(pointer);
  }
  result(pointer, maximum) {
    const p = Number(pointer), memory = this.w.memory.buffer;
    need(p >= 0 && p + 8 <= memory.byteLength, "Invalid Wasm result pointer");
    const n = Number(new DataView(memory).getBigUint64(p, true));
    need(n <= maximum && p + 8 + n * 8 <= memory.byteLength, "Invalid Wasm result length");
    return new Uint8Array(memory, p + 8, n * 8).slice();
  }
}

export class Gpt2 {
  static async load(notify = () => {}) {
    need(isSecureContext && navigator.gpu, "Open this page on localhost or HTTPS in a browser with WebGPU enabled.");
    const manifestResponse = await fetch("manifest.json", { cache: "no-store" });
    need(manifestResponse.ok, "Cannot load manifest");
    const manifest = await manifestResponse.json();
    need(manifest.schemaVersion === 2 && manifest.contextTokens === 128, "Unsupported artifact bundle");
    async function artifact(name) {
      const response = await fetch(name);
      need(response.ok, `Cannot load ${name}`);
      const bytes = await response.arrayBuffer();
      need(bytes.byteLength === manifest.sizes[name], `${name}: wrong byte count`);
      need(hex(await crypto.subtle.digest("SHA-256", bytes)) === manifest.sha256[name], `${name}: SHA-256 mismatch`);
      return bytes;
    }
    const runner = Object.assign(new Gpt2(), { manifest, failure: null, busy: false, dispatches: 0 });
    for (const name of ["model", "tokenizer", "transfer"]) {
      notify(`Loading ${name}.wasm`);
      const { instance } = await WebAssembly.instantiate(await artifact(`${name}.wasm`), {});
      runner[name] = new Wasm(instance.exports);
    }
    runner.table = new Uint8Array(await artifact("tokenizer.bin"));
    runner.params = new Uint8Array(await artifact("params.bin"));
    notify("Loading token and position embeddings");
    new Uint8Array(runner.transfer.w.memory.buffer, 0, 154782720).set(new Uint8Array(await artifact("embedding.bin")));
    const adapter = await navigator.gpu.requestAdapter();
    need(adapter, "No WebGPU adapter available");
    const device = await adapter.requestDevice();
    runner.device = device;
    try {
      device.lost.then(info => { runner.failure = Error(`WebGPU device lost: ${info.message}`); });
      device.addEventListener("uncapturederror", event => { runner.failure = Error(event.error.message); });
      runner.adapterInfo = adapter.info ? `${adapter.info.vendor} ${adapter.info.architecture} ${adapter.info.description}`.trim() : "Browser WebGPU";
      const buffer = (size, usage) => device.createBuffer({ size, usage });
      runner.a = buffer(3072 * 4, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST);
      runner.c = buffer(25129 * 4, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC);
      runner.read = buffer(25129 * 4, GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST);
      runner.pipelines = [];
      device.pushErrorScope("validation");
      for (const shape of manifest.shapes) {
        notify(`Compiling WGSL: 1 × ${shape.cols} × ${shape.inner}`);
        const module = device.createShaderModule({ code: new TextDecoder().decode(await artifact(shape.shader)) });
        runner.pipelines.push(await device.createComputePipelineAsync({ layout: "auto", compute: { module, entryPoint: manifest.shaderEntryPoint ?? "gemm_f32" } }));
      }
      runner.groups = []; runner.weights = [];
      for (const [index, matrix] of manifest.matrices.entries()) {
        notify(`Loading pretrained matrices · ${index + 1}/50`);
        const shape = manifest.shapes[matrix.shape], bytes = await artifact(matrix.file);
        need(bytes.byteLength === shape.inner * shape.cols * 4, "Matrix shape mismatch");
        const b = buffer(bytes.byteLength, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST);
        device.queue.writeBuffer(b, 0, bytes);
        runner.weights.push(b);
        runner.groups.push(device.createBindGroup({ layout: runner.pipelines[matrix.shape].getBindGroupLayout(0), entries: [
          { binding: 0, resource: { buffer: runner.a, size: shape.inner * 4 } },
          { binding: 1, resource: { buffer: b } },
          { binding: 2, resource: { buffer: runner.c, size: shape.cols * 4 } },
        ] }));
      }
      const error = await device.popErrorScope();
      need(!error, error?.message);
      await device.queue.onSubmittedWorkDone();
      if (runner.failure) throw runner.failure;
      return runner;
    } catch (error) { device.destroy(); throw error; }
  }

  compute(op, x, aux, params, position, expected) {
    const m = this.model; m.w.reset();
    const inputs = [BigInt(op), m.array(x), m.array(aux), m.array(params), BigInt(position)];
    const result = m.result(m.w.compute(...inputs), expected);
    need(result.byteLength === expected * 8, "Model rejected stage inputs");
    return result;
  }
  tokenize(op, input) {
    const m = this.tokenizer; m.w.reset();
    const table = m.array(this.table), values = m.array(input);
    return m.result(m.w.tokens(BigInt(op), table, values), 65536);
  }
  encode(text) {
    const bytes = new TextEncoder().encode(text);
    need(bytes.length > 0 && bytes.length <= 16384, "Enter 1–16,384 UTF-8 bytes of prompt text.");
    const result = this.tokenize(0, words(Array.from(bytes)));
    const tokens = Array.from({ length: result.length / 8 }, (_, i) => Number(word(result, i)));
    need(tokens.length > 0 && tokens.every(t => t < 50257), "Tokenizer rejected the prompt");
    return tokens;
  }
  decode(token) {
    const result = this.tokenize(1, words([token]));
    const bytes = new Uint8Array(result.length / 8);
    for (let i = 0; i < bytes.length; i++) { const b = word(result, i); need(b < 256n, "Invalid decoded byte"); bytes[i] = Number(b); }
    return bytes;
  }
  parameter(offset, length) { return this.params.subarray(offset * 8, (offset + length) * 8); }
  embedding(index, kind) {
    this.transfer.w.embedding(BigInt(index), BigInt(kind));
    return new Uint8Array(this.transfer.w.memory.buffer, F64, 768 * 8).slice();
  }
  async dispatch(matrix, x) {
    if (this.failure) throw this.failure;
    const shapeId = this.manifest.matrices[matrix].shape, shape = this.manifest.shapes[shapeId];
    need(x.length === shape.inner * 8, "Matrix input shape mismatch");
    const transfer = this.transfer.w, device = this.device;
    new Uint8Array(transfer.memory.buffer, F64, x.length).set(x);
    transfer.convert(0n, BigInt(shape.inner));
    device.queue.writeBuffer(this.a, 0, transfer.memory.buffer, F32, shape.inner * 4);
    const encoder = device.createCommandEncoder(), pass = encoder.beginComputePass();
    pass.setPipeline(this.pipelines[shapeId]); pass.setBindGroup(0, this.groups[matrix]);
    pass.dispatchWorkgroups(Math.ceil(shape.cols / 8), 1, 1); pass.end();
    encoder.copyBufferToBuffer(this.c, 0, this.read, 0, shape.cols * 4);
    device.queue.submit([encoder.finish()]);
    await this.read.mapAsync(GPUMapMode.READ, 0, shape.cols * 4);
    try { new Uint8Array(transfer.memory.buffer, F32, shape.cols * 4).set(new Uint8Array(this.read.getMappedRange(0, shape.cols * 4))); }
    finally { this.read.unmap(); }
    if (this.failure) throw this.failure;
    transfer.convert(1n, BigInt(shape.cols)); this.dispatches++;
    return new Uint8Array(transfer.memory.buffer, F64, shape.cols * 8).slice();
  }
  async forward(token, position, head) {
    let x = this.compute(0, this.embedding(token, 0), this.embedding(position, 1), EMPTY, 0, 768);
    for (let layer = 0; layer < 12; layer++) {
      const o = layer * 9984;
      let n = this.compute(1, x, EMPTY, this.parameter(o, 1536), 0, 768);
      const qkv = await this.dispatch(layer * 4, n);
      const attention = this.compute(2, qkv, this.cache[layer], this.parameter(o + 1536, 2304), position, 2304);
      this.cache[layer].set(attention.subarray(0, 768 * 8), position * 768 * 8);
      this.cache[layer].set(attention.subarray(768 * 8, 1536 * 8), (128 * 768 + position * 768) * 8);
      let projection = await this.dispatch(layer * 4 + 1, attention.subarray(1536 * 8));
      x = this.compute(3, x, projection, this.parameter(o + 3840, 768), 0, 768);
      n = this.compute(1, x, EMPTY, this.parameter(o + 4608, 1536), 0, 768);
      const expanded = await this.dispatch(layer * 4 + 2, n);
      const activated = this.compute(4, expanded, EMPTY, this.parameter(o + 6144, 3072), 0, 3072);
      projection = await this.dispatch(layer * 4 + 3, activated);
      x = this.compute(3, x, projection, this.parameter(o + 9216, 768), 0, 768);
    }
    if (!head) return EMPTY;
    x = this.compute(1, x, EMPTY, this.parameter(12 * 9984, 1536), 0, 768);
    const left = await this.dispatch(48, x), right = await this.dispatch(49, x);
    const logits = new Uint8Array(50257 * 8); logits.set(left); logits.set(right, left.length); return logits;
  }

  async generate({ prompt, count, temperature, seed, stopped, onProgress, onBytes }) {
    need(!this.busy, "Generation is already running");
    need(Number.isInteger(count) && count > 0 && count < 128, "Request 1–127 new tokens");
    need(Number.isInteger(seed) && seed > 0 && seed <= 0xffffffff, "Seed must be 1–4,294,967,295");
    const temperatures = { "0": 0n, "0.7": 0x3fe6666666666666n, "0.8": 0x3fe999999999999an, "1": 0x3ff0000000000000n };
    need(Object.hasOwn(temperatures, temperature), "Unsupported temperature");
    const tokens = this.encode(prompt);
    need(tokens.length + count <= 128, `The prompt has ${tokens.length} tokens. Request at most ${128 - tokens.length} new tokens.`);
    this.busy = true; this.cache = Array.from({ length: 12 }, () => new Uint8Array(196608 * 8));
    let logits, state = BigInt(seed), produced = 0, reason = "limit";
    try {
      for (let i = 0; i < tokens.length; i++) {
        if (stopped()) return { produced, reason: "stopped", promptTokens: tokens.length };
        onProgress(`Reading prompt · ${i + 1}/${tokens.length} tokens`);
        logits = await this.forward(tokens[i], i, i + 1 === tokens.length);
      }
      for (let step = 0; step < count; step++) {
        if (stopped()) { reason = "stopped"; break; }
        const picked = this.compute(5, logits, EMPTY, words([temperatures[temperature], 40n, state]), 0, 2);
        const token = Number(word(picked, 0)); state = word(picked, 1);
        need(token < 50257, "Sampled token out of range");
        if (token === 50256) { reason = "end of text"; break; }
        onBytes(this.decode(token)); produced++;
        onProgress(`Writing · ${produced}/${count} tokens`);
        if (step + 1 < count) logits = await this.forward(token, tokens.length + step, true);
      }
      return { produced, reason, promptTokens: tokens.length };
    } finally { this.busy = false; this.cache = null; }
  }
  destroy() { this.device.destroy(); }
}
