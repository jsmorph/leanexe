// Two hosts for the commands of Examples/Gpt32/HostProgram.lean, as leanexe-webgpu-host's session mode
// runs them: `load NAME PATH`, `words NAME u32:W,...`, `output NAME N`, `shader NAME PATH`, and
// `run SHADER WORKGROUPS OUT IN...`.  GpuHost dispatches each `run` on WebGPU with the kernel's
// WGSL text.  WasmHost calls the same kernel in gpt32.wasm, where a buffer is an array in the
// module's memory with the same words: the length, then each element's binary32 bits in the low
// half of an 8-byte word.

// The argument kinds of each kernel, from `kernelOf` in Examples/Gpt32/Specs.lean, and the
// function of gpt32.wasm that computes it.
const KINDS = {
  embed: ["array", "array", "word", "word", "word"],
  layerNorm: ["array", "array", "array", "word", "float"],
  linear: ["array", "array", "array", "word", "word"],
  append: ["array", "array", "word", "word"],
  scores: ["array", "array", "word", "word", "word"],
  headMax: ["array", "word", "word"],
  headSum: ["array", "array", "word", "word"],
  probs: ["array", "array", "array", "word", "word"],
  mix: ["array", "array", "word", "word"],
  add: ["array", "array"],
  gelu: ["array"],
  logits: ["array", "array", "word", "word"],
};
const EXPORTS = { gelu: "geluArray32" };
const exportOf = kernel => EXPORTS[kernel] ?? `${kernel}32`;
const kernelOf = shader => shader.replace(/^@/, "");

export function parseWords(spec) {
  if (!spec.startsWith("u32:")) throw Error(`unsupported words: ${spec}`);
  return Uint32Array.from(spec.slice(4).split(",").map(Number));
}

/** The command `line`, split into its name and arguments. */
export function parse(line) {
  const [command, ...args] = line.split(" ");
  return { command, args };
}

export class GpuHost {
  static async open(choice) {
    if (!globalThis.isSecureContext) {
      throw Error("This page is not a secure context, so the browser hides WebGPU. " +
                  "Open it at http://127.0.0.1 or http://localhost, or through HTTPS.");
    }
    if (!navigator.gpu) throw Error("navigator.gpu is undefined: this browser has no WebGPU, or it is off.");
    const options = choice === "fallback" ? { forceFallbackAdapter: true } : { powerPreference: choice };
    const adapter = await navigator.gpu.requestAdapter(options);
    if (!adapter) throw Error(`The browser returned no adapter for "${choice}".`);
    const device = await adapter.requestDevice();
    return new GpuHost(adapter, device);
  }

  constructor(adapter, device) {
    this.adapter = adapter;
    this.device = device;
    this.buffers = new Map();
    this.pipelines = new Map();
    this.dispatches = 0;
    this.errors = [];
    this.lost = null;
    device.lost.then(info => { this.lost = `device lost: ${info.reason} ${info.message}`; });
    device.addEventListener("uncapturederror", e => this.errors.push(e.error.message));
  }

  describe() {
    const info = this.adapter.info ?? {};
    return `${info.vendor || "?"} ${info.architecture || "?"}` +
      (info.description ? ` (${info.description})` : "") +
      ((info.isFallbackAdapter ?? this.adapter.isFallbackAdapter) ? ", fallback adapter" : "");
  }

  check() {
    if (this.lost) throw Error(this.lost);
    if (this.errors.length > 0) throw Error(`WebGPU error: ${this.errors[0]}`);
  }

  set(name, buffer) {
    this.buffers.get(name)?.destroy();
    this.buffers.set(name, buffer);
  }

  fromWords(words) {
    const buffer = this.device.createBuffer({ size: words.byteLength,
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC | GPUBufferUsage.COPY_DST });
    this.device.queue.writeBuffer(buffer, 0, words.buffer, words.byteOffset, words.byteLength);
    return buffer;
  }

  async shader(name, path) {
    const response = await fetch(path, { cache: "no-store" });
    if (!response.ok) throw Error(`cannot load ${path}`);
    const module = this.device.createShaderModule({ code: await response.text(), label: name });
    const info = await module.getCompilationInfo();
    const errors = info.messages.filter(m => m.type === "error");
    if (errors.length > 0) throw Error(`${name}: ${errors.map(m => m.message).join("; ")}`);
    this.pipelines.set(name, await this.device.createComputePipelineAsync({
      label: name, layout: "auto", compute: { module, entryPoint: "main" } }));
    return info.messages.map(m => `${name}: ${m.type} ${m.lineNum}:${m.linePos} ${m.message}`);
  }

  load(name, bytes) {
    this.set(name, this.fromWords(new Uint32Array(bytes)));
  }

  words(name, words) {
    this.set(name, this.fromWords(words));
  }

  output(name, n) {
    const words = new Uint32Array(2 + 2 * n);
    words[0] = n;
    this.set(name, this.fromWords(words));
  }

  run(shader, workgroups, out, ins) {
    const pipeline = this.pipelines.get(shader);
    if (!pipeline) throw Error(`no shader named ${shader}`);
    const entries = [...ins, out].map((name, binding) => {
      const buffer = this.buffers.get(name);
      if (!buffer) throw Error(`no buffer named ${name}`);
      return { binding, resource: { buffer } };
    });
    const group = this.device.createBindGroup({ layout: pipeline.getBindGroupLayout(0), entries });
    const encoder = this.device.createCommandEncoder();
    const pass = encoder.beginComputePass();
    pass.setPipeline(pipeline);
    pass.setBindGroup(0, group);
    pass.dispatchWorkgroups(workgroups);
    pass.end();
    this.device.queue.submit([encoder.finish()]);
    this.dispatches++;
  }

  /** The binary32 elements of the buffer `name`. */
  async floats(name) {
    const buffer = this.buffers.get(name);
    const read = this.device.createBuffer({ size: buffer.size,
      usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST });
    const encoder = this.device.createCommandEncoder();
    encoder.copyBufferToBuffer(buffer, 0, read, 0, buffer.size);
    this.device.queue.submit([encoder.finish()]);
    await read.mapAsync(GPUMapMode.READ);
    const words = new Uint32Array(read.getMappedRange());
    const n = words[0];
    const bits = new Uint32Array(n);
    for (let i = 0; i < n; i++) bits[i] = words[2 + 2 * i];
    read.unmap();
    read.destroy();
    this.check();
    return new Float32Array(bits.buffer);
  }

  close() {
    this.device.destroy();
  }
}

export class WasmHost {
  static async open(path) {
    const { instance } = await WebAssembly.instantiateStreaming(fetch(path, { cache: "no-store" }));
    return new WasmHost(instance.exports);
  }

  constructor(exports) {
    this.x = exports;
    this.values = new Map();
    this.calls = 0;
    this.count = null;
  }

  describe() {
    return `gpt32.wasm, ${(this.x.memory.buffer.byteLength / 2 ** 20).toFixed(0)} MiB of memory`;
  }

  bytes(ptr, length) {
    return new Uint8Array(this.x.memory.buffer, ptr, length);
  }

  allocate(bytes) {
    const ptr = Number(this.x.alloc(BigInt(bytes.byteLength)));
    this.bytes(ptr, bytes.byteLength).set(bytes);
    return ptr;
  }

  set(name, value) {
    const old = this.values.get(name);
    if (old?.array !== undefined) this.x.release(BigInt(old.array));
    this.values.set(name, value);
  }

  load(name, bytes) {
    this.set(name, { array: this.allocate(new Uint8Array(bytes)) });
  }

  words(name, words) {
    this.set(name, { words });
  }

  output(name, n) {
    this.count = n;
  }

  argument(name, kind) {
    const value = this.values.get(name);
    if (!value) throw Error(`no buffer named ${name}`);
    if (kind === "array") {
      if (value.array === undefined) {
        value.array = this.allocate(new Uint8Array(value.words.buffer, value.words.byteOffset,
                                                   value.words.byteLength));
      }
      return BigInt(value.array);
    }
    if (kind === "word") return BigInt(value.words[0]) | (BigInt(value.words[1]) << 32n);
    return new Float32Array(Uint32Array.of(value.words[0]).buffer)[0];
  }

  run(shader, workgroups, out, ins) {
    const kernel = kernelOf(shader);
    const kinds = KINDS[kernel];
    if (!kinds || kinds.length !== ins.length) throw Error(`no kernel ${kernel} with ${ins.length} arguments`);
    const args = ins.map((name, i) => this.argument(name, kinds[i]));
    const ptr = Number(this.x[exportOf(kernel)](...args));
    const n = Number(new DataView(this.x.memory.buffer).getBigUint64(ptr, true));
    if (n !== this.count) throw Error(`${kernel} returned ${n} elements; the output has ${this.count}`);
    this.set(out, { array: ptr });
    this.calls++;
  }

  async floats(name) {
    const ptr = this.values.get(name).array;
    const view = new DataView(this.x.memory.buffer);
    const n = Number(view.getBigUint64(ptr, true));
    const bits = new Uint32Array(n);
    for (let i = 0; i < n; i++) bits[i] = view.getUint32(ptr + 8 + 8 * i, true);
    return new Float32Array(bits.buffer);
  }

  close() {}
}

/** Top-k sampling with `sampleTopK` of gpt.wasm, the binary64 model's module, which
`sampleTopK_implements` proves computes `Examples.Gpt.sampleTopK`: the scores, widened
to binary64, `k`, the temperature, and a SplitMix64 state give the token and the next state.  It
borrows the scores, so the caller releases them. */
export class Sampler {
  static async open(path) {
    const { instance } = await WebAssembly.instantiateStreaming(fetch(path, { cache: "no-store" }));
    return new Sampler(instance.exports);
  }

  constructor(exports) {
    this.x = exports;
  }

  sample(chunks, k, temperature, state) {
    const n = chunks.reduce((total, chunk) => total + chunk.length, 0);
    const ptr = this.x.alloc(BigInt(8 + 8 * n));
    const base = Number(ptr);
    const view = new DataView(this.x.memory.buffer);
    view.setBigUint64(base, BigInt(n), true);
    let i = 0;
    for (const chunk of chunks) {
      for (const score of chunk) view.setFloat64(base + 8 + 8 * i++, score, true);
    }
    const [token, next] = this.x.sampleTopK(ptr, BigInt(k), temperature, state);
    this.x.release(ptr);
    return { token: Number(token), next: BigInt.asUintN(64, next) };
  }
}

/** Runs the command lines on each host, fetching each weight file once. */
export async function runLines(lines, hosts, progress = () => {}) {
  const messages = [];
  for (const line of lines) {
    const { command, args } = parse(line);
    if (command === "load") {
      const response = await fetch(args[1], { cache: "no-store" });
      if (!response.ok) throw Error(`cannot load ${args[1]}`);
      const bytes = await response.arrayBuffer();
      progress(args[0], bytes.byteLength);
      for (const host of hosts) host.load(args[0], bytes);
    } else if (command === "shader") {
      for (const host of hosts) if (host instanceof GpuHost) messages.push(...await host.shader(args[0], args[1]));
    } else if (command === "words") {
      const words = parseWords(args[1]);
      for (const host of hosts) host.words(args[0], words);
    } else if (command === "output") {
      for (const host of hosts) host.output(args[0], Number(args[1]));
    } else if (command === "run") {
      for (const host of hosts) host.run(args[0], Number(args[1]), args[2], args.slice(3));
    } else {
      throw Error(`unknown command: ${line}`);
    }
  }
  return messages;
}
