#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.Correctness";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "refcount");

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args[0]} failed`);
  }
}

function compile(entry, out) {
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
}

async function instantiate(entry) {
  const out = path.join(outDir, `${entry}.wasm`);
  compile(entry, out);
  const bytes = fs.readFileSync(out);
  const { instance } = await WebAssembly.instantiate(bytes, {});
  for (const name of ["alloc", "reset", "retain", "release", "free"]) {
    if (typeof instance.exports[name] !== "function") {
      throw new Error(`${entry}: missing export ${name}`);
    }
  }
  return instance.exports;
}

function pointer(value) {
  return Number(BigInt.asUintN(64, value));
}

async function checkArrayReleaseReuse() {
  const exports = await instantiate("structureArrayReturn");
  const result = exports.structureArrayReturn();
  const ptr = pointer(result[0]);
  const len = new DataView(exports.memory.buffer).getBigUint64(ptr, true);
  if (len !== 2n) {
    throw new Error(`structureArrayReturn: expected length 2, got ${len}`);
  }
  exports.release(BigInt(ptr));
  const reused = pointer(exports.alloc(16n));
  if (reused !== ptr) {
    throw new Error(`release did not reuse array block: expected ${ptr}, got ${reused}`);
  }
}

async function checkRetainDelaysReuse() {
  const exports = await instantiate("structureArrayReturn");
  const ptr = pointer(exports.structureArrayReturn()[0]);
  exports.retain(BigInt(ptr));
  exports.release(BigInt(ptr));
  const afterOneRelease = pointer(exports.alloc(16n));
  if (afterOneRelease === ptr) {
    throw new Error("retain did not preserve the block after one release");
  }
  exports.release(BigInt(ptr));
  const afterSecondRelease = pointer(exports.alloc(16n));
  if (afterSecondRelease !== ptr) {
    throw new Error(`second release did not free retained block: expected ${ptr}, got ${afterSecondRelease}`);
  }
}

async function checkFreeAlias() {
  const exports = await instantiate("byteArrayStringConstReturn");
  const result = exports.byteArrayStringConstReturn();
  const ptr = pointer(result[0]);
  const len = pointer(result[1]);
  const bytes = Array.from(new Uint8Array(exports.memory.buffer, ptr, len));
  if (bytes.join(",") !== "88,89,90") {
    throw new Error(`byteArrayStringConstReturn: unexpected bytes ${bytes.join(",")}`);
  }
  exports.free(BigInt(ptr));
  const reused = pointer(exports.alloc(BigInt(len)));
  if (reused !== ptr) {
    throw new Error(`free alias did not reuse byte block: expected ${ptr}, got ${reused}`);
  }
}

async function main() {
  run(["lake", "build", moduleName]);
  fs.mkdirSync(outDir, { recursive: true });
  await checkArrayReleaseReuse();
  await checkRetainDelaysReuse();
  await checkFreeAlias();
  process.stdout.write("checked 3 refcount cases\n");
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
