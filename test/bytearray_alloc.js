#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.ByteArrayPrograms";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "bytearray-programs");

function run(args) {
  return runChecked(args, { encoding: "utf8" });
}

function compile(entry, out) {
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
}

function instantiate(entry) {
  const out = path.join(outDir, `${entry}.wasm`);
  compile(entry, out);
  return { entry, wasm: out };
}

function callByteArray(exports, input, args = []) {
  return host.callI64(exports.wasm, exports.entry, [
    host.byteArray(input),
    ...args.map((arg) => host.i64(arg)),
  ]);
}

function callByteArrayOutput(exports, input) {
  return host.callBytes(exports.wasm, exports.entry, [host.byteArray(input)]);
}

function callNoInputByteArrayOutput(exports) {
  return host.callBytes(exports.wasm, exports.entry);
}

function callScalarByteArray(exports, prefix, input) {
  return host.callI64(exports.wasm, exports.entry, [host.i64(prefix), host.byteArray(input)]);
}

function readByteArrayResult(_exports, result) {
  return result;
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

  const readUInt64LE = await instantiate("readUInt64LE");
  const readUInt64BE = await instantiate("readUInt64BE");
  const uint64Bytes = new Uint8Array([1, 2, 3, 4, 5, 6, 7, 8]);
  const uint64LE = callByteArray(readUInt64LE, uint64Bytes);
  if (uint64LE !== 578437695752307201n) {
    throw new Error(`readUInt64LE: expected 578437695752307201, got ${uint64LE}`);
  }
  const uint64BE = callByteArray(readUInt64BE, uint64Bytes);
  if (uint64BE !== 72623859790382856n) {
    throw new Error(`readUInt64BE: expected 72623859790382856, got ${uint64BE}`);
  }

  const foldSum = await instantiate("foldSum");
  const foldSumCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([1, 2, 3]), expected: 6n },
    { input: new Uint8Array([255, 1]), expected: 256n },
  ];

  for (const testCase of foldSumCases) {
    const actual = callByteArray(foldSum, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`foldSum: expected ${testCase.expected}, got ${actual}`);
    }
  }

  const foldWindowDecimal = await instantiate("foldWindowDecimal");
  const foldWindowDecimalCases = [
    { input: new Uint8Array([]), expected: 0n },
    { input: new Uint8Array([9]), expected: 0n },
    { input: new Uint8Array([9, 4, 5, 6]), expected: 45n },
  ];

  for (const testCase of foldWindowDecimalCases) {
    const actual = callByteArray(foldWindowDecimal, testCase.input);
    if (actual !== testCase.expected) {
      throw new Error(`foldWindowDecimal: expected ${testCase.expected}, got ${actual}`);
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

  const mkABC = await instantiate("mkABC");
  const mkABCActual = callNoInputByteArrayOutput(mkABC);
  if (!sameBytes(mkABCActual, new Uint8Array([65, 66, 67]))) {
    throw new Error(`mkABC: expected 65,66,67, got ${Array.from(mkABCActual)}`);
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

  const appendABCXYZ = await instantiate("appendABCXYZ");
  const appendABCXYZActual = callNoInputByteArrayOutput(appendABCXYZ);
  if (!sameBytes(appendABCXYZActual, new Uint8Array([65, 66, 67, 88, 89, 90]))) {
    throw new Error(`appendABCXYZ: expected 65,66,67,88,89,90, got ${Array.from(appendABCXYZActual)}`);
  }

  const appendInputABC = await instantiate("appendInputABC");
  const appendInputABCCases = [
    { input: new Uint8Array([]), expected: new Uint8Array([65, 66, 67]) },
    { input: new Uint8Array([48, 49]), expected: new Uint8Array([48, 49, 65, 66, 67]) },
  ];

  for (const testCase of appendInputABCCases) {
    const actual = readByteArrayResult(appendInputABC, callByteArrayOutput(appendInputABC, testCase.input));
    if (!sameBytes(actual, testCase.expected)) {
      throw new Error(`appendInputABC: expected ${Array.from(testCase.expected)}, got ${Array.from(actual)}`);
    }
  }

  const appendNotationABCXYZ = await instantiate("appendNotationABCXYZ");
  const appendNotationABCXYZActual = callNoInputByteArrayOutput(appendNotationABCXYZ);
  if (!sameBytes(appendNotationABCXYZActual, new Uint8Array([65, 66, 67, 88, 89, 90]))) {
    throw new Error(
      `appendNotationABCXYZ: expected 65,66,67,88,89,90, got ${Array.from(appendNotationABCXYZActual)}`,
    );
  }

  const setABC = await instantiate("setABC");
  const setABCActual = callNoInputByteArrayOutput(setABC);
  if (!sameBytes(setABCActual, new Uint8Array([65, 90, 67]))) {
    throw new Error(`setABC: expected 65,90,67, got ${Array.from(setABCActual)}`);
  }

  const setFirstBang = await instantiate("setFirstBang");
  const setFirstBangCases = [
    { input: new Uint8Array([]), expected: new Uint8Array([]) },
    { input: new Uint8Array([65]), expected: new Uint8Array([33]) },
    { input: new Uint8Array([65, 66]), expected: new Uint8Array([33, 66]) },
  ];

  for (const testCase of setFirstBangCases) {
    const actual = readByteArrayResult(setFirstBang, callByteArrayOutput(setFirstBang, testCase.input));
    if (!sameBytes(actual, testCase.expected)) {
      throw new Error(`setFirstBang: expected ${Array.from(testCase.expected)}, got ${Array.from(actual)}`);
    }
  }

  const setBangABC = await instantiate("setBangABC");
  const setBangABCActual = callNoInputByteArrayOutput(setBangABC);
  if (!sameBytes(setBangABCActual, new Uint8Array([65, 66, 90]))) {
    throw new Error(`setBangABC: expected 65,66,90, got ${Array.from(setBangABCActual)}`);
  }

  const setBangFirstQuestion = await instantiate("setBangFirstQuestion");
  const setBangFirstQuestionCases = [
    { input: new Uint8Array([]), expected: new Uint8Array([]) },
    { input: new Uint8Array([65]), expected: new Uint8Array([63]) },
    { input: new Uint8Array([65, 66]), expected: new Uint8Array([63, 66]) },
  ];

  for (const testCase of setBangFirstQuestionCases) {
    const actual = readByteArrayResult(setBangFirstQuestion, callByteArrayOutput(setBangFirstQuestion, testCase.input));
    if (!sameBytes(actual, testCase.expected)) {
      throw new Error(`setBangFirstQuestion: expected ${Array.from(testCase.expected)}, got ${Array.from(actual)}`);
    }
  }

  const copyInputMiddle = await instantiate("copyInputMiddle");
  const copyInputMiddleCases = [
    { input: new Uint8Array([]), expected: new Uint8Array([65, 66, 67]) },
    { input: new Uint8Array([88]), expected: new Uint8Array([65, 66, 67]) },
    { input: new Uint8Array([88, 89, 90, 91]), expected: new Uint8Array([65, 89, 90]) },
  ];

  for (const testCase of copyInputMiddleCases) {
    const actual = readByteArrayResult(copyInputMiddle, callByteArrayOutput(copyInputMiddle, testCase.input));
    if (!sameBytes(actual, testCase.expected)) {
      throw new Error(`copyInputMiddle: expected ${Array.from(testCase.expected)}, got ${Array.from(actual)}`);
    }
  }

  const copyInputPastDest = await instantiate("copyInputPastDest");
  const copyInputPastDestCases = [
    { input: new Uint8Array([]), expected: new Uint8Array([65, 66, 67]) },
    { input: new Uint8Array([88]), expected: new Uint8Array([65, 66, 67, 88]) },
    { input: new Uint8Array([88, 89, 90]), expected: new Uint8Array([65, 66, 67, 88, 89]) },
  ];

  for (const testCase of copyInputPastDestCases) {
    const actual = readByteArrayResult(copyInputPastDest, callByteArrayOutput(copyInputPastDest, testCase.input));
    if (!sameBytes(actual, testCase.expected)) {
      throw new Error(`copyInputPastDest: expected ${Array.from(testCase.expected)}, got ${Array.from(actual)}`);
    }
  }

  const copyShortSource = await instantiate("copyShortSource");
  const copyShortSourceActual = callNoInputByteArrayOutput(copyShortSource);
  if (!sameBytes(copyShortSourceActual, new Uint8Array([65, 88, 67]))) {
    throw new Error(`copyShortSource: expected 65,88,67, got ${Array.from(copyShortSourceActual)}`);
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
    2 +
    foldSumCases.length +
    foldWindowDecimalCases.length +
    emptyViaIsEmptyCases.length +
    1 +
    1 +
    appendBangCases.length +
    1 +
    appendInputABCCases.length +
    1 +
    1 +
    setFirstBangCases.length +
    1 +
    setBangFirstQuestionCases.length +
    copyInputMiddleCases.length +
    copyInputPastDestCases.length +
    1 +
    tailSliceCases.length;
  process.stdout.write(`checked ${total} bytearray allocation cases\n`);
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
