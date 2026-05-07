#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

function toHex(bytes) {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join("");
}

function leanEval(leanExe, hex) {
  const result = spawnSync(leanExe, ["eval", "--hex", hex], {
    encoding: "utf8",
  });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || "Lean evaluator failed");
  }
  return Number(result.stdout.trim());
}

function randomBytes(length) {
  const bytes = new Uint8Array(length);
  for (let i = 0; i < length; i++) {
    bytes[i] = Math.floor(Math.random() * 256);
  }
  return bytes;
}

async function main() {
  const wasmPath = process.argv[2] || path.join("build", "validate.wasm");
  const cases = Number(process.argv[3] || "200");
  const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");

  if (!fs.existsSync(wasmPath)) {
    const emit = spawnSync(leanExe, [
      "compile",
      "--module",
      "LeanExe.Examples.AsciiDigits",
      "--entry",
      "LeanExe.Examples.AsciiDigits.validateGeneric",
      "--out",
      wasmPath,
    ], { encoding: "utf8" });
    if (emit.status !== 0) {
      throw new Error(emit.stderr.trim() || "Wasm emission failed");
    }
  }

  const wasm = fs.readFileSync(wasmPath);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const { memory, alloc, reset, validate, validateGeneric } = instance.exports;
  if (!memory) {
    throw new Error("Wasm module does not export memory");
  }

  function runWasm(input) {
    if (typeof validateGeneric === "function") {
      let ptr = 1024;
      if (typeof alloc === "function" && typeof reset === "function") {
        reset();
        ptr = Number(alloc(BigInt(input.length)));
      }
      new Uint8Array(memory.buffer, ptr, input.length).set(input);
      return Number(validateGeneric(BigInt(ptr), BigInt(input.length)));
    }

    if (typeof validate === "function" && typeof alloc === "function" && typeof reset === "function") {
      reset();
      const ptr = alloc(input.length);
      new Uint8Array(memory.buffer, ptr, input.length).set(input);
      return Number(validate(ptr, input.length));
    }

    throw new Error("Wasm module does not export a supported validator ABI");
  }

  const fixed = [
    new Uint8Array([]),
    new Uint8Array([0x30]),
    new Uint8Array([0x39]),
    new Uint8Array([0x2f]),
    new Uint8Array([0x3a]),
    new Uint8Array([0x31, 0x32, 0x33, 0x34]),
  ];

  for (const input of fixed) {
    const hex = toHex(input);
    const wasmValue = runWasm(input);
    const leanValue = leanEval(leanExe, hex);
    if (wasmValue !== leanValue) {
      throw new Error(`mismatch for ${hex}: Lean ${leanValue}, Wasm ${wasmValue}`);
    }
  }

  for (let i = 0; i < cases; i++) {
    const input = randomBytes(Math.floor(Math.random() * 128));
    const hex = toHex(input);
    const wasmValue = runWasm(input);
    const leanValue = leanEval(leanExe, hex);
    if (wasmValue !== leanValue) {
      throw new Error(`mismatch for ${hex}: Lean ${leanValue}, Wasm ${wasmValue}`);
    }
  }

  process.stdout.write(`checked ${fixed.length + cases} cases\n`);
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
