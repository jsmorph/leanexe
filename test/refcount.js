#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const correctnessModule = "LeanExe.Examples.Correctness";
const byteArrayModule = "LeanExe.Examples.ByteArrayPrograms";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "refcount");

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args[0]} failed`);
  }
}

function compile(moduleName, entry, out) {
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
}

async function instantiate(moduleName, entry) {
  const out = path.join(outDir, `${moduleName}.${entry}.wasm`);
  compile(moduleName, entry, out);
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

function writeU64Array(exports, values) {
  const ptr = pointer(exports.alloc(BigInt(8 + values.length * 8)));
  const view = new DataView(exports.memory.buffer);
  view.setBigUint64(ptr, BigInt(values.length), true);
  values.forEach((value, index) => {
    view.setBigUint64(ptr + 8 + index * 8, BigInt(value), true);
  });
  return ptr;
}

async function checkArrayReleaseReuse() {
  const exports = await instantiate(correctnessModule, "structureArrayReturn");
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
  const exports = await instantiate(correctnessModule, "structureArrayReturn");
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
  const exports = await instantiate(correctnessModule, "byteArrayStringConstReturn");
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

async function checkCompilerReleasesScalarTemp() {
  const exports = await instantiate(byteArrayModule, "firstBytePlusArray");
  exports.reset();
  const probeInput = pointer(exports.alloc(1n));
  const expectedTempBlock = pointer(exports.alloc(16n));
  exports.reset();
  const input = pointer(exports.alloc(1n));
  if (input !== probeInput) {
    throw new Error(`reset did not restore heap start: expected ${probeInput}, got ${input}`);
  }
  new Uint8Array(exports.memory.buffer, input, 1)[0] = 37;
  const result = pointer(exports.firstBytePlusArray(BigInt(input), 1n));
  if (result !== 42) {
    throw new Error(`firstBytePlusArray: expected 42, got ${result}`);
  }
  const reused = pointer(exports.alloc(16n));
  if (reused !== expectedTempBlock) {
    throw new Error(`compiler did not release scalar temporary: expected ${expectedTempBlock}, got ${reused}`);
  }
}

async function checkAllocatorGrowsMemory() {
  const exports = await instantiate(correctnessModule, "byteArrayStringConstReturn");
  exports.reset();
  const beforeBytes = exports.memory.buffer.byteLength;
  const len = BigInt(beforeBytes);
  const ptr = pointer(exports.alloc(len));
  const afterBytes = exports.memory.buffer.byteLength;
  if (afterBytes <= beforeBytes) {
    throw new Error(`alloc did not grow memory: before ${beforeBytes}, after ${afterBytes}`);
  }
  if (ptr + beforeBytes > afterBytes) {
    throw new Error(`grown allocation exceeds memory: ptr ${ptr}, len ${beforeBytes}, memory ${afterBytes}`);
  }
  new Uint8Array(exports.memory.buffer, ptr + beforeBytes - 1, 1)[0] = 123;
}

async function checkByteArrayOwnerChildRelease() {
  const exports = await instantiate(correctnessModule, "byteArrayStructReplicateRuntimeReleaseFrees");
  const actual = pointer(exports.byteArrayStructReplicateRuntimeReleaseFrees());
  if (actual !== 202) {
    throw new Error(`byteArrayStructReplicateRuntimeReleaseFrees: expected 202, got ${actual}`);
  }
}

async function checkArrayOwnerChildRelease() {
  const nested = await instantiate(correctnessModule, "nestedArrayRuntimeReleaseFrees");
  const nestedActual = pointer(nested.nestedArrayRuntimeReleaseFrees());
  if (nestedActual !== 202) {
    throw new Error(`nestedArrayRuntimeReleaseFrees: expected 202, got ${nestedActual}`);
  }

  const structField = await instantiate(correctnessModule, "structArrayFieldRuntimeReleaseFrees");
  const structActual = pointer(structField.structArrayFieldRuntimeReleaseFrees());
  if (structActual !== 202) {
    throw new Error(`structArrayFieldRuntimeReleaseFrees: expected 202, got ${structActual}`);
  }
}

async function checkBorrowedArrayNoopRelease() {
  const popped = await instantiate(correctnessModule, "borrowedArrayPopEmptyReleaseFrees");
  const emptyPtr = writeU64Array(popped, []);
  const poppedActual = pointer(popped.borrowedArrayPopEmptyReleaseFrees(BigInt(emptyPtr)));
  if (poppedActual !== 0) {
    throw new Error(`borrowedArrayPopEmptyReleaseFrees: expected 0, got ${poppedActual}`);
  }
  popped.release(BigInt(emptyPtr));

  const setOob = await instantiate(correctnessModule, "borrowedArraySetOobReleaseFrees");
  const setPtr = writeU64Array(setOob, [7, 8]);
  const setActual = pointer(setOob.borrowedArraySetOobReleaseFrees(BigInt(setPtr)));
  if (setActual !== 0) {
    throw new Error(`borrowedArraySetOobReleaseFrees: expected 0, got ${setActual}`);
  }
  setOob.release(BigInt(setPtr));

  const reversed = await instantiate(correctnessModule, "borrowedArrayReverseSingletonReleaseFrees");
  const singletonPtr = writeU64Array(reversed, [7]);
  const reversedActual = pointer(
    reversed.borrowedArrayReverseSingletonReleaseFrees(BigInt(singletonPtr)),
  );
  if (reversedActual !== 0) {
    throw new Error(`borrowedArrayReverseSingletonReleaseFrees: expected 0, got ${reversedActual}`);
  }
  reversed.release(BigInt(singletonPtr));
}

async function main() {
  run(["lake", "build", correctnessModule]);
  run(["lake", "build", byteArrayModule]);
  fs.mkdirSync(outDir, { recursive: true });
  await checkArrayReleaseReuse();
  await checkRetainDelaysReuse();
  await checkFreeAlias();
  await checkCompilerReleasesScalarTemp();
  await checkAllocatorGrowsMemory();
  await checkByteArrayOwnerChildRelease();
  await checkArrayOwnerChildRelease();
  await checkBorrowedArrayNoopRelease();
  process.stdout.write("checked 11 refcount cases\n");
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
