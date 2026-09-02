#!/usr/bin/env node

const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "selfhost");
const wasm = path.join(outDir, "emitter-stage1.wasm");
const image = path.join(outDir, "emitter-stage1.image");
const reproduced = path.join(outDir, "emitter-stage2.wasm");
const moduleName = "LeanExe.Wasm.Image.Emit";
const sourceEntry = "LeanExe.Wasm.Image.emitImage";
const exportEntry = "emitImage";

function compileInputs() {
  fs.mkdirSync(outDir, { recursive: true });
  runChecked([
    leanExe,
    "compile",
    "--module",
    moduleName,
    "--entry",
    sourceEntry,
    "--out",
    wasm,
  ], { encoding: "utf8", stdio: "inherit" });
  runChecked([
    leanExe,
    "compile-image",
    "--module",
    moduleName,
    "--entry",
    sourceEntry,
    "--out",
    image,
  ], { encoding: "utf8", stdio: "inherit" });
}

function callExceptBytes(input) {
  const commands = [`alloc 1 ${input.length}`];
  const chunkSize = 4096;
  for (let offset = 0; offset < input.length; offset += chunkSize) {
    const chunk = input.subarray(offset, Math.min(offset + chunkSize, input.length));
    commands.push(`write-bytes 1 ${offset} ${chunk.toString("hex")}`);
  }
  commands.push("arg-ptr 1", `arg-u64 ${input.length}`);
  const result = host.script(wasm, commands, exportEntry, 5, [
    "read-memory result:1 result:2",
    "read-memory result:3 result:4",
  ]);
  const tag = Number(result.slots[0]);
  if (tag !== 0 && tag !== 1) {
    throw new Error(`emitImage returned invalid Except tag ${tag}`);
  }
  const ptrIndex = tag === 0 ? 1 : 3;
  const lenIndex = ptrIndex + 1;
  const ptr = result.slots[ptrIndex];
  const length = Number(result.slots[lenIndex]);
  const chunk = result.memoryChunks.find(
    (item) => item.start === ptr && item.bytes.length === length,
  );
  if (!chunk) {
    throw new Error(`emitImage result memory ${ptr}+${length} was not returned by the host`);
  }
  return { tag, bytes: Buffer.from(chunk.bytes) };
}

function callExceptBytesJavaScript(moduleBytes, input) {
  const instance = new WebAssembly.Instance(new WebAssembly.Module(moduleBytes), {});
  const exports = instance.exports;
  exports.reset();
  const inputPtr = Number(exports.alloc(BigInt(input.length)));
  new Uint8Array(exports.memory.buffer, inputPtr, input.length).set(input);
  const slots = exports[exportEntry](BigInt(inputPtr), BigInt(input.length));
  const tag = Number(slots[0]);
  if (tag !== 0 && tag !== 1) {
    throw new Error(`JavaScript host received invalid Except tag ${tag}`);
  }
  const ptrIndex = tag === 0 ? 1 : 3;
  const ptr = Number(slots[ptrIndex]);
  const length = Number(slots[ptrIndex + 1]);
  return {
    tag,
    bytes: Buffer.from(new Uint8Array(exports.memory.buffer, ptr, length)),
  };
}

function digest(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function firstDifference(left, right) {
  const limit = Math.min(left.length, right.length);
  for (let index = 0; index < limit; index += 1) {
    if (left[index] !== right[index]) return index;
  }
  return left.length === right.length ? -1 : limit;
}

function main() {
  if (!process.argv.includes("--use-existing")) {
    compileInputs();
  }
  if (!fs.existsSync(wasm) || !fs.existsSync(image)) {
    throw new Error("self-host inputs are missing; run without --use-existing first");
  }

  const expected = fs.readFileSync(wasm);
  const result = callExceptBytes(fs.readFileSync(image));
  if (result.tag === 0) {
    throw new Error(`emitImage rejected its self image: ${result.bytes.toString("utf8")}`);
  }
  fs.writeFileSync(reproduced, result.bytes);
  const difference = firstDifference(expected, result.bytes);
  if (difference !== -1) {
    throw new Error(
      `self-host mismatch at byte ${difference}: Stage 1 is ${expected.length} bytes, ` +
        `Stage 2 is ${result.bytes.length} bytes`,
    );
  }

  const repeated = callExceptBytesJavaScript(result.bytes, fs.readFileSync(image));
  if (repeated.tag === 0) {
    throw new Error(`Stage 2 rejected its self image: ${repeated.bytes.toString("utf8")}`);
  }
  const repeatedDifference = firstDifference(result.bytes, repeated.bytes);
  if (repeatedDifference !== -1) {
    throw new Error(`Stage 2 fixed-point mismatch at byte ${repeatedDifference}`);
  }

  const malformed = callExceptBytes(Buffer.from("bad image", "utf8"));
  if (malformed.tag !== 0 || malformed.bytes.toString("utf8") !== "leanexe-image: invalid magic") {
    throw new Error(`unexpected malformed-image result: tag ${malformed.tag}, bytes ${malformed.bytes}`);
  }

  process.stdout.write(
    `Wasmtime Stage 1 and JavaScript Stage 2 reproduced ${expected.length} bytes; ` +
      `SHA-256 ${digest(expected)}\n`,
  );
  process.stdout.write(`self image is ${fs.statSync(image).size} bytes; SHA-256 ${digest(fs.readFileSync(image))}\n`);
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
