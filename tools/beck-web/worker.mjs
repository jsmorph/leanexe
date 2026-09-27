import { encode, check } from "./scenarios.mjs";

self.onmessage = async ({ data: input }) => {
  try {
    const words = encode(input);
    const response = await fetch("/program.wasm");
    if (!response.ok) throw new Error(`WASM download failed (${response.status}).`);
    const { instance } = await WebAssembly.instantiate(await response.arrayBuffer());
    const wasm = instance.exports;
    const pointer = wasm.alloc(BigInt(8 * (words.length + 1)));
    const start = Number(pointer);
    if (!Number.isSafeInteger(start) || start < 0 || start + 8 * (words.length + 1) > wasm.memory.buffer.byteLength) {
      throw new Error("WASM returned an invalid input address.");
    }
    const inputView = new DataView(wasm.memory.buffer);
    inputView.setBigUint64(start, BigInt(words.length), true);
    words.forEach((word, index) => inputView.setBigUint64(start + 8 * (index + 1), BigInt(word), true));
    const began = performance.now();
    const output = Number(wasm.compute(pointer));
    const milliseconds = performance.now() - began;
    const view = new DataView(wasm.memory.buffer);
    if (!Number.isSafeInteger(output) || output < 0 || output + 8 > view.byteLength) {
      throw new Error("WASM returned an invalid output address.");
    }
    const size = Number(view.getBigUint64(output, true));
    if (size < 1 || size > input.jobs.length + 2 || output + 8 * (size + 1) > view.byteLength) {
      throw new Error("WASM returned an invalid output length.");
    }
    const result = Array.from({ length: size }, (_, index) => Number(view.getBigUint64(output + 8 * (index + 1), true)));
    self.postMessage({ ok: true, ...check(input, result), milliseconds, memoryBytes: wasm.memory.buffer.byteLength });
  } catch (error) {
    self.postMessage({ ok: false, message: error.message });
  }
};
