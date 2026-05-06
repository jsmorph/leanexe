#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

function parseHex(hex) {
  if (hex.length % 2 !== 0) {
    throw new Error("hex input has odd length");
  }

  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    const value = Number.parseInt(hex.slice(i * 2, i * 2 + 2), 16);
    if (Number.isNaN(value)) {
      throw new Error("invalid hex input");
    }
    bytes[i] = value;
  }
  return bytes;
}

async function main() {
  const wasmPath = process.argv[2] || path.join("build", "validate.wasm");
  const hex = process.argv[3] || "";
  const input = parseHex(hex);
  const wasm = fs.readFileSync(wasmPath);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const { memory, alloc, reset, validate } = instance.exports;

  reset();
  const ptr = alloc(input.length);
  new Uint8Array(memory.buffer, ptr, input.length).set(input);
  process.stdout.write(`${validate(ptr, input.length)}\n`);
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
