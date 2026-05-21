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

function writeBytes(exports, values) {
  const ptr = pointer(exports.alloc(BigInt(values.length)));
  new Uint8Array(exports.memory.buffer, ptr, values.length).set(values);
  return ptr;
}

function samePointers(left, right) {
  if (left.length !== right.length) {
    return false;
  }
  const sortedLeft = [...left].sort((a, b) => a - b);
  const sortedRight = [...right].sort((a, b) => a - b);
  return sortedLeft.every((value, index) => value === sortedRight[index]);
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

  const optionBytes = await instantiate(correctnessModule, "optionByteArrayArrayRuntimeReleaseFrees");
  const optionBytesActual = pointer(optionBytes.optionByteArrayArrayRuntimeReleaseFrees());
  if (optionBytesActual !== 302) {
    throw new Error(`optionByteArrayArrayRuntimeReleaseFrees: expected 302, got ${optionBytesActual}`);
  }

  const tokens = await instantiate(correctnessModule, "publicTokenArrayRuntimeReleaseFrees");
  const tokensActual = pointer(tokens.publicTokenArrayRuntimeReleaseFrees());
  if (tokensActual !== 302) {
    throw new Error(`publicTokenArrayRuntimeReleaseFrees: expected 302, got ${tokensActual}`);
  }

  const groups = await instantiate(correctnessModule, "byteArrayGroupArrayRuntimeReleaseFrees");
  const groupsActual = pointer(groups.byteArrayGroupArrayRuntimeReleaseFrees());
  if (groupsActual !== 403) {
    throw new Error(`byteArrayGroupArrayRuntimeReleaseFrees: expected 403, got ${groupsActual}`);
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

async function checkCompilerReleasesOwnedCallResults() {
  const array = await instantiate(correctnessModule, "ownedArrayCallTempScalar");
  array.reset();
  const expectedArrayBlock = pointer(array.alloc(16n));
  array.reset();
  const arrayResult = pointer(array.ownedArrayCallTempScalar());
  if (arrayResult !== 5) {
    throw new Error(`ownedArrayCallTempScalar: expected 5, got ${arrayResult}`);
  }
  const reusedArrayBlock = pointer(array.alloc(16n));
  if (reusedArrayBlock !== expectedArrayBlock) {
    throw new Error(
      `compiler did not release array call result: expected ${expectedArrayBlock}, got ${reusedArrayBlock}`,
    );
  }

  const bytes = await instantiate(correctnessModule, "ownedByteArrayCallTempScalar");
  bytes.reset();
  const expectedByteBlock = pointer(bytes.alloc(1n));
  bytes.reset();
  const byteResult = pointer(bytes.ownedByteArrayCallTempScalar());
  if (byteResult !== 66) {
    throw new Error(`ownedByteArrayCallTempScalar: expected 66, got ${byteResult}`);
  }
  const reusedByteBlock = pointer(bytes.alloc(1n));
  if (reusedByteBlock !== expectedByteBlock) {
    throw new Error(
      `compiler did not release byte-array call result: expected ${expectedByteBlock}, got ${reusedByteBlock}`,
    );
  }

  const arrayParam = await instantiate(correctnessModule, "ownedArrayParamCallTempScalarFromInput");
  arrayParam.reset();
  const probeArrayInput = writeU64Array(arrayParam, [5]);
  const expectedArrayParamBlock = pointer(arrayParam.alloc(24n));
  arrayParam.reset();
  const arrayInput = writeU64Array(arrayParam, [5]);
  if (arrayInput !== probeArrayInput) {
    throw new Error(`reset did not restore array input block: expected ${probeArrayInput}, got ${arrayInput}`);
  }
  const arrayParamResult = pointer(arrayParam.ownedArrayParamCallTempScalarFromInput(BigInt(arrayInput)));
  if (arrayParamResult !== 16) {
    throw new Error(`ownedArrayParamCallTempScalarFromInput: expected 16, got ${arrayParamResult}`);
  }
  const reusedArrayParamBlock = pointer(arrayParam.alloc(24n));
  if (reusedArrayParamBlock !== expectedArrayParamBlock) {
    throw new Error(
      `compiler did not release heap-parameter array call result: expected ${expectedArrayParamBlock}, got ${reusedArrayParamBlock}`,
    );
  }

  const bytesParam = await instantiate(correctnessModule, "ownedByteArrayParamCallTempScalarFromInput");
  bytesParam.reset();
  const probeByteInput = pointer(bytesParam.alloc(1n));
  const expectedByteParamBlock = pointer(bytesParam.alloc(2n));
  bytesParam.reset();
  const byteInput = pointer(bytesParam.alloc(1n));
  if (byteInput !== probeByteInput) {
    throw new Error(`reset did not restore byte input block: expected ${probeByteInput}, got ${byteInput}`);
  }
  new Uint8Array(bytesParam.memory.buffer, byteInput, 1)[0] = 65;
  const byteParamResult = pointer(
    bytesParam.ownedByteArrayParamCallTempScalarFromInput(BigInt(byteInput), 1n),
  );
  if (byteParamResult !== 100) {
    throw new Error(`ownedByteArrayParamCallTempScalarFromInput: expected 100, got ${byteParamResult}`);
  }
  const reusedByteParamBlock = pointer(bytesParam.alloc(2n));
  if (reusedByteParamBlock !== expectedByteParamBlock) {
    throw new Error(
      `compiler did not release heap-parameter byte-array call result: expected ${expectedByteParamBlock}, got ${reusedByteParamBlock}`,
    );
  }

  const byteHeapResultStats = await instantiate(correctnessModule, "byteArrayResultDropsOwnedTempStats");
  const byteResultActual = pointer(byteHeapResultStats.byteArrayResultDropsOwnedTempStats());
  if (byteResultActual !== 10101) {
    throw new Error(`byteArrayResultDropsOwnedTempStats: expected 10101, got ${byteResultActual}`);
  }

  const recursive = await instantiate(correctnessModule, "ownedRecursiveNodeParamCallTempScalar");
  recursive.reset();
  const expectedRecursiveBlocks = [
    pointer(recursive.alloc(32n)),
    pointer(recursive.alloc(32n)),
    pointer(recursive.alloc(32n)),
  ];
  recursive.reset();
  const recursiveResult = pointer(recursive.ownedRecursiveNodeParamCallTempScalar());
  if (recursiveResult !== 310) {
    throw new Error(`ownedRecursiveNodeParamCallTempScalar: expected 310, got ${recursiveResult}`);
  }
  const reusedRecursiveBlocks = [
    pointer(recursive.alloc(32n)),
    pointer(recursive.alloc(32n)),
    pointer(recursive.alloc(32n)),
  ];
  if (!samePointers(reusedRecursiveBlocks, expectedRecursiveBlocks)) {
    throw new Error(
      `compiler did not release recursive call result: expected ${expectedRecursiveBlocks.join(",")}, got ${reusedRecursiveBlocks.join(",")}`,
    );
  }

  const box = await instantiate(correctnessModule, "ownedBoxCallTempScalar");
  box.reset();
  const expectedBoxArrayBlock = pointer(box.alloc(16n));
  const expectedBoxByteBlock = pointer(box.alloc(1n));
  box.reset();
  const boxResult = pointer(box.ownedBoxCallTempScalar());
  if (boxResult !== 13) {
    throw new Error(`ownedBoxCallTempScalar: expected 13, got ${boxResult}`);
  }
  const reusedBoxArrayBlock = pointer(box.alloc(16n));
  const reusedBoxByteBlock = pointer(box.alloc(1n));
  if (reusedBoxArrayBlock !== expectedBoxArrayBlock) {
    throw new Error(
      `compiler did not release boxed array call result: expected ${expectedBoxArrayBlock}, got ${reusedBoxArrayBlock}`,
    );
  }
  if (reusedBoxByteBlock !== expectedBoxByteBlock) {
    throw new Error(
      `compiler did not release boxed byte-array call result: expected ${expectedBoxByteBlock}, got ${reusedBoxByteBlock}`,
    );
  }
}

async function checkCompilerReleasesFoldAccumulators() {
  const cases = [
    ["arrayFoldByteArrayAccumulatorReleaseStats", 30202],
    ["arrayFoldOptionByteArrayAccumulatorReleaseStats", 30502],
    ["arrayFoldPublicTokenAccumulatorReleaseStats", 30402],
    ["arrayFoldByteArrayGroupAccumulatorReleaseStats", 30502],
    ["byteArrayFoldByteArrayAccumulatorReleaseStats", 30202],
    ["idRunByteArrayForOutputReleaseStats", 30202],
    ["idRunRangeForByteArrayOutputReleaseStats", 30202],
    ["arrayFoldRecursiveAccumulatorReleaseStats", 30606],
  ];
  for (const [entry, expected] of cases) {
    const exports = await instantiate(correctnessModule, entry);
    const actual = pointer(exports[entry]());
    if (actual !== expected) {
      throw new Error(`${entry}: expected ${expected}, got ${actual}`);
    }
  }

  const arrayInput = await instantiate(correctnessModule, "arrayFoldInputByteArrayAccumulatorReleaseStats");
  const arrayInputPtr = writeU64Array(arrayInput, [65, 66, 67]);
  const arrayInputActual = pointer(
    arrayInput.arrayFoldInputByteArrayAccumulatorReleaseStats(BigInt(arrayInputPtr)),
  );
  if (arrayInputActual !== 30202) {
    throw new Error(`arrayFoldInputByteArrayAccumulatorReleaseStats: expected 30202, got ${arrayInputActual}`);
  }

  const byteInput = await instantiate(correctnessModule, "byteArrayFoldInputByteArrayAccumulatorReleaseStats");
  const byteInputPtr = writeBytes(byteInput, [1, 2, 3]);
  const byteInputActual = pointer(
    byteInput.byteArrayFoldInputByteArrayAccumulatorReleaseStats(BigInt(byteInputPtr), 3n),
  );
  if (byteInputActual !== 30202) {
    throw new Error(`byteArrayFoldInputByteArrayAccumulatorReleaseStats: expected 30202, got ${byteInputActual}`);
  }
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
  await checkCompilerReleasesOwnedCallResults();
  await checkCompilerReleasesFoldAccumulators();
  process.stdout.write("checked 31 refcount cases\n");
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
