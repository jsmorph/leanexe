#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.ByteArrayPrograms";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "bytearray-programs");

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args[0]} failed`);
  }
  return result;
}

function writeInput(memory, ptr, input) {
  new Uint8Array(memory.buffer, ptr, input.length).set(input);
}

function compile(entry, out) {
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
}

async function instantiate(entry) {
  const out = path.join(outDir, `${entry}.wasm`);
  compile(entry, out);
  const wasm = fs.readFileSync(out);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const fn = instance.exports[entry];
  if (typeof fn !== "function") {
    throw new Error(`compiled module does not export ${entry}`);
  }
  const { memory, alloc, reset } = instance.exports;
  if (!memory || typeof alloc !== "function" || typeof reset !== "function") {
    throw new Error("compiled module does not export memory, alloc, and reset");
  }
  return { memory, alloc, reset, fn };
}

function callByteArray(exports, input, args = []) {
  return withByteArray(exports, input, (ptr, len) => exports.fn(ptr, len, ...args));
}

function callByteArrayOutput(exports, input) {
  return withByteArrayRaw(exports, input, (ptr, len) => exports.fn(ptr, len));
}

function callNoInputByteArrayOutput(exports) {
  exports.reset();
  return readByteArrayResult(exports, exports.fn());
}

function callScalarByteArray(exports, prefix, input) {
  return withByteArray(exports, input, (ptr, len) => exports.fn(prefix, ptr, len));
}

function withByteArray(exports, input, call) {
  return BigInt.asUintN(64, withByteArrayRaw(exports, input, call));
}

function withByteArrayRaw(exports, input, call) {
  exports.reset();
  const ptr = Number(exports.alloc(BigInt(input.length)));
  writeInput(exports.memory, ptr, input);
  return call(BigInt(ptr), BigInt(input.length));
}

function readByteArrayResult(exports, result) {
  if (!Array.isArray(result) || result.length !== 2) {
    throw new Error(`expected ByteArray result, got ${result}`);
  }
  const ptr = Number(BigInt.asUintN(64, result[0]));
  const len = Number(BigInt.asUintN(64, result[1]));
  return Uint8Array.from(new Uint8Array(exports.memory.buffer, ptr, len));
}

function sameBytes(left, right) {
  if (left.length !== right.length) {
    return false;
  }
  for (let index = 0; index < left.length; index += 1) {
    if (left[index] !== right[index]) {
      return false;
    }
  }
  return true;
}

function fnv1a32(input) {
  let hash = 2166136261;
  for (const byte of input) {
    hash ^= byte;
    hash = Math.imul(hash, 16777619) >>> 0;
  }
  return BigInt(hash);
}

async function main() {
  run(["lake", "build", moduleName]);
  fs.mkdirSync(outDir, { recursive: true });

  const firstBytePlusArray = await instantiate("firstBytePlusArray");
  const firstBytePlusArrayCases = [
    { input: new Uint8Array([]), expected: 5n },
    { input: new Uint8Array([37]), expected: 42n },
    { input: new Uint8Array([255]), expected: 260n },
  ];

  for (const testCase of firstBytePlusArrayCases) {
    const actual = callByteArray(firstBytePlusArray, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstBytePlusArray: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteIsStar = await instantiate("firstByteIsStar");
  const firstByteIsStarCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([42]), expected: 1n },
    { input: new Uint8Array([41]), expected: 0n },
  ];

  for (const testCase of firstByteIsStarCases) {
    const actual = callByteArray(firstByteIsStar, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteIsStar: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteNextIsZero = await instantiate("firstByteNextIsZero");
  const firstByteNextIsZeroCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([255]), expected: 1n },
    { input: new Uint8Array([254]), expected: 0n },
  ];

  for (const testCase of firstByteNextIsZeroCases) {
    const actual = callByteArray(firstByteNextIsZero, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteNextIsZero: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteLowNibble = await instantiate("firstByteLowNibble");
  const firstByteLowNibbleCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([0xab]), expected: 11n },
    { input: new Uint8Array([0xf0]), expected: 0n },
  ];

  for (const testCase of firstByteLowNibbleCases) {
    const actual = callByteArray(firstByteLowNibble, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteLowNibble: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const firstByteBangIndex = await instantiate("firstByteBangIndex");
  const firstByteBangIndexCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([37]), expected: 37n },
    { input: new Uint8Array([255]), expected: 255n },
  ];

  for (const testCase of firstByteBangIndexCases) {
    const actual = callByteArray(firstByteBangIndex, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`firstByteBangIndex: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const byteAtOrZero = await instantiate("byteAtOrZero");
  const byteAtOrZeroCases = [
    { input: new Uint8Array([10, 20, 30]), args: [0n], expected: 10n },
    { input: new Uint8Array([10, 20, 30]), args: [2n], expected: 30n },
    { input: new Uint8Array([10, 20, 30]), args: [3n], expected: 0n },
  ];

  for (const testCase of byteAtOrZeroCases) {
    const actual = callByteArray(byteAtOrZero, testCase.input, testCase.args);
    if (actual !== testCase.expected) {
      throw new Error(`byteAtOrZero: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const byteAtQuestionOrZero = await instantiate("byteAtQuestionOrZero");
  const byteAtQuestionOrZeroCases = [
    { input: new Uint8Array([10, 20, 30]), args: [0n], expected: 10n },
    { input: new Uint8Array([10, 20, 30]), args: [2n], expected: 30n },
    { input: new Uint8Array([10, 20, 30]), args: [3n], expected: 0n },
  ];

  for (const testCase of byteAtQuestionOrZeroCases) {
    const actual = callByteArray(byteAtQuestionOrZero, testCase.input, testCase.args);
    if (actual !== testCase.expected) {
      throw new Error(`byteAtQuestionOrZero: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const byteAtProofOrZero = await instantiate("byteAtProofOrZero");
  const byteAtProofOrZeroCases = [
    { input: new Uint8Array([42]), expected: 42n },
    { input: new Uint8Array([]), expected: 0n },
  ];

  for (const testCase of byteAtProofOrZeroCases) {
    const actual = callByteArray(byteAtProofOrZero, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`byteAtProofOrZero: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const sliceSecondPlusSize = await instantiate("sliceSecondPlusSize");
  const sliceSecondPlusSizeCases = [
    { input: new Uint8Array([10, 20, 30, 40]), expected: 22n },
    { input: new Uint8Array([10]), expected: 0n },
  ];

  for (const testCase of sliceSecondPlusSizeCases) {
    const actual = callByteArray(sliceSecondPlusSize, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`sliceSecondPlusSize: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const sliceClampSize = await instantiate("sliceClampSize");
  const sliceClampSizeCases = [
    { input: new Uint8Array([10, 20, 30, 40]), expected: 3n },
    { input: new Uint8Array([]), expected: 0n },
  ];

  for (const testCase of sliceClampSizeCases) {
    const actual = callByteArray(sliceClampSize, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`sliceClampSize: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const sliceStopBeforeStart = await instantiate("sliceStopBeforeStart");
  const sliceStopBeforeStartCases = [
    { input: new Uint8Array([10, 20, 30, 40]), expected: 0n },
  ];

  for (const testCase of sliceStopBeforeStartCases) {
    const actual = callByteArray(sliceStopBeforeStart, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`sliceStopBeforeStart: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const prefixPlusFirstByte = await instantiate("prefixPlusFirstByte");
  const prefixPlusFirstByteCases = [
    { prefix: 5n, input: new Uint8Array([]), expected: 5n },
    { prefix: 5n, input: new Uint8Array([37]), expected: 42n },
    { prefix: 5n, input: new Uint8Array([255]), expected: 260n },
  ];

  for (const testCase of prefixPlusFirstByteCases) {
    const actual = callScalarByteArray(prefixPlusFirstByte, testCase.prefix, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`prefixPlusFirstByte: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const fnv1a32Program = await instantiate("fnv1a32");
  const fnv1a32Cases = [
    { input: new Uint8Array([]) },
    { input: new Uint8Array([97]) },
    { input: new Uint8Array([104, 101, 108, 108, 111]) },
  ];

  for (const testCase of fnv1a32Cases) {
    const expected = fnv1a32(testCase.input);
    const actual = callByteArray(fnv1a32Program, testCase.input);
    if (actual !== expected) {
      throw new Error(`fnv1a32: expected ${expected}, got ${actual}`);
    }
  }

  const emptyViaIsEmpty = await instantiate("emptyViaIsEmpty");
  const emptyViaIsEmptyCases = [
    { input: new Uint8Array([]), expected: 1n },
    { input: new Uint8Array([1]), expected: 0n },
  ];

  for (const testCase of emptyViaIsEmptyCases) {
    const actual = callByteArray(emptyViaIsEmpty, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`emptyViaIsEmpty: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const bytesABC = await instantiate("bytesABC");
  const bytesABCActual = callNoInputByteArrayOutput(bytesABC);
  if (!sameBytes(bytesABCActual, new Uint8Array([65, 66, 67]))) {
    throw new Error(`bytesABC: expected 65,66,67, got ${Array.from(bytesABCActual)}`);
  }

  const appendBang = await instantiate("appendBang");
  const appendBangCases = [
    { input: new Uint8Array([]), expected: new Uint8Array([33]) },
    { input: new Uint8Array([65, 66]), expected: new Uint8Array([65, 66, 33]) },
  ];

  for (const testCase of appendBangCases) {
    const actual = readByteArrayResult(appendBang, callByteArrayOutput(appendBang, testCase.input));
    if (!sameBytes(actual, testCase.expected)) {
      throw new Error(`appendBang: expected ${Array.from(testCase.expected)}, got ${Array.from(actual)}`);
    }
  }

  const tailSlice = await instantiate("tailSlice");
  const tailSliceCases = [
    { input: new Uint8Array([]), expected: new Uint8Array([]) },
    { input: new Uint8Array([65]), expected: new Uint8Array([]) },
    { input: new Uint8Array([65, 66, 67]), expected: new Uint8Array([66, 67]) },
  ];

  for (const testCase of tailSliceCases) {
    const actual = readByteArrayResult(tailSlice, callByteArrayOutput(tailSlice, testCase.input));
    if (!sameBytes(actual, testCase.expected)) {
      throw new Error(`tailSlice: expected ${Array.from(testCase.expected)}, got ${Array.from(actual)}`);
    }
  }

  const total =
    firstBytePlusArrayCases.length +
    firstByteIsStarCases.length +
    firstByteNextIsZeroCases.length +
    firstByteLowNibbleCases.length +
    firstByteBangIndexCases.length +
    byteAtOrZeroCases.length +
    byteAtQuestionOrZeroCases.length +
    byteAtProofOrZeroCases.length +
    sliceSecondPlusSizeCases.length +
    sliceClampSizeCases.length +
    sliceStopBeforeStartCases.length +
    prefixPlusFirstByteCases.length +
    fnv1a32Cases.length +
    emptyViaIsEmptyCases.length +
    1 +
    appendBangCases.length +
    tailSliceCases.length;
  process.stdout.write(`checked ${total} bytearray allocation cases\n`);
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
