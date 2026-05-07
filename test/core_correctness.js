#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.Correctness";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "core-correctness");

const accepted = [
  { name: "shortOrSkipsTrap", args: [], expected: 1n },
  { name: "shortAndSkipsTrap", args: [], expected: 0n },
  { name: "divByZero", args: [], expected: 0n },
  { name: "modByZero", args: [], expected: 5n },
  { name: "overflow", args: [], expected: 0n },
  { name: "underflow", args: [], expected: 18446744073709551615n },
  { name: "natSubSaturates", args: [], expected: 0n },
  { name: "natSubNormal", args: [], expected: 2n },
  { name: "natAddNormal", args: [], expected: 8n },
  { name: "natMulNormal", args: [], expected: 42n },
  { name: "bitwiseOrXor", args: [], expected: 6n },
  { name: "shiftMasking", args: [], expected: 42n },
  { name: "uint64OfNatValue", args: [41n], expected: 42n },
  { name: "uint64OfHugeNat", args: [], expected: 0n },
  { name: "wrappedUInt8Literal", args: [], expected: 44n },
  { name: "uint8OfNatValue", args: [298n], expected: 43n },
  { name: "uint8AddWrap", args: [], expected: 0n },
  { name: "uint8SubWrap", args: [], expected: 255n },
  { name: "uint8MulWrap", args: [], expected: 16n },
  { name: "uint8DivModZero", args: [], expected: 7n },
  { name: "nestedShadow", args: [3n], expected: 64n },
  { name: "unusedScalarLetSkipsTrap", args: [], expected: 1n },
  { name: "letUsedOnlyInUnusedProductField", args: [], expected: 7n },
  { name: "ignoredCallArgSkipsTrap", args: [], expected: 1n },
  { name: "callArgUsedOnlyInUnusedProductField", args: [], expected: 7n },
  { name: "callArgLets", args: [7n], expected: 809n },
  { name: "productLet", args: [], expected: 12n },
  { name: "nestedProduct", args: [], expected: 203n },
  { name: "productSkipsUnusedField", args: [], expected: 7n },
  { name: "productBranch", args: [0n], expected: 12n },
  { name: "productBranch", args: [1n], expected: 34n },
  { name: "arrayUpdateRead", args: [], expected: 110n },
  { name: "arraySizeAfterSet", args: [], expected: 3n },
  { name: "arrayPushRead", args: [], expected: 507n },
  { name: "nonzeroReplicateRead", args: [], expected: 77n },
  { name: "arrayPopRead", args: [], expected: 44n },
  { name: "productArrayAlias", args: [], expected: 2211n },
  { name: "recLetDemo", args: [], expected: 518n },
  { name: "recExitDemo", args: [], expected: 314n },
  { name: "recProductDemo", args: [], expected: 10n },
  { name: "recursiveDemandedFuelGet", args: [], expected: 7n },
  { name: "optionSomeMatch", args: [], expected: 8n },
  { name: "optionNoneMatchSkipsSomeArm", args: [], expected: 5n },
  { name: "optionSomeMatchSkipsUnusedPayload", args: [], expected: 9n },
  { name: "optionLet", args: [], expected: 18n },
  { name: "optionBranch", args: [0n], expected: 11n },
  { name: "optionBranch", args: [1n], expected: 34n },
  { name: "natComparisons", args: [2n], expected: 10n },
  { name: "natComparisons", args: [3n], expected: 20n },
  { name: "natComparisons", args: [6n], expected: 30n },
  { name: "u64Comparisons", args: [2n], expected: 10n },
  { name: "u64Comparisons", args: [3n], expected: 20n },
  { name: "u64Comparisons", args: [6n], expected: 30n },
  { name: "greaterComparisons", args: [2n], expected: 10n },
  { name: "greaterComparisons", args: [3n], expected: 20n },
  { name: "greaterComparisons", args: [6n], expected: 30n },
  { name: "boolMatchScalar", args: [0n], expected: 10n },
  { name: "boolMatchScalar", args: [1n], expected: 20n },
  { name: "boolMatchSkipsTrap", args: [], expected: 7n },
  { name: "boolMatchCondition", args: [0n], expected: 1n },
  { name: "boolMatchCondition", args: [1n], expected: 2n },
  { name: "boolMatchProduct", args: [0n], expected: 12n },
  { name: "boolMatchProduct", args: [1n], expected: 34n },
  { name: "decideNatLt", args: [2n], expected: 1n },
  { name: "decideNatLt", args: [3n], expected: 2n },
  { name: "decideUInt64Ge", args: [2n], expected: 0n },
  { name: "decideUInt64Ge", args: [3n], expected: 1n },
  { name: "propEqNat", args: [3n], expected: 1n },
  { name: "propEqNat", args: [4n], expected: 2n },
  { name: "decideEqUInt64", args: [3n], expected: 1n },
  { name: "decideEqUInt64", args: [4n], expected: 0n },
  { name: "propEqBoolSkipsTrap", args: [], expected: 1n },
  { name: "propAndNat", args: [3n], expected: 1n },
  { name: "propAndNat", args: [1n], expected: 2n },
  { name: "propOrNat", args: [1n], expected: 1n },
  { name: "propOrNat", args: [3n], expected: 2n },
  { name: "propOrNat", args: [6n], expected: 1n },
  { name: "propNotNat", args: [2n], expected: 2n },
  { name: "propNotNat", args: [3n], expected: 1n },
  { name: "propOrSkipsTrap", args: [], expected: 1n },
  { name: "propAndSkipsTrap", args: [], expected: 0n },
];

const rejected = [
  {
    name: "rejectProductReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectProductReturn",
  },
  {
    name: "rejectProductParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectProductParam",
  },
  {
    name: "rejectOptionReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectOptionReturn",
  },
  {
    name: "rejectOptionParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectOptionParam",
  },
  {
    name: "rejectByteArrayReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectByteArrayReturn",
  },
  {
    name: "rejectUInt8Param",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUInt8Param",
  },
  {
    name: "rejectUInt8Return",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUInt8Return",
  },
  {
    name: "alloc",
    message: "entry export name is reserved by the runtime ABI: alloc",
  },
  {
    name: "rejectHugeNatLiteral",
    message: "Nat literal exceeds bounded runtime representation: 18446744073709551616",
  },
  {
    name: "rejectRecursiveIgnoredTrapArg",
    message: "strict call may evaluate an argument not demanded by callee: LeanExe.Examples.Correctness.recIgnoreTrapArgFuel",
  },
  {
    name: "rejectRecursiveIgnoredHiddenTrapArg",
    message: "strict call may evaluate an argument not demanded by callee: LeanExe.Examples.Correctness.recIgnoreTrapArgFuel",
  },
  {
    name: "rejectHigherOrder",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectHigherOrder",
  },
  {
    name: "rejectIO",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectIO",
  },
];

const trapped = [
  { name: "natAddOverflow", args: [] },
  { name: "natMulOverflow", args: [] },
];

function run(args) {
  return spawnSync(args[0], args.slice(1), { encoding: "utf8" });
}

function compile(name, out) {
  return run([
    leanExe,
    "compile",
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${name}`,
    "--out",
    out,
  ]);
}

async function runAccepted(testCase) {
  const out = path.join(outDir, `${testCase.name}.wasm`);
  const compiled = compile(testCase.name, out);
  if (compiled.status !== 0) {
    throw new Error(`${testCase.name} failed to compile: ${compiled.stderr.trim()}`);
  }

  const wasm = fs.readFileSync(out);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const fn = instance.exports[testCase.name];
  if (typeof fn !== "function") {
    throw new Error(`${testCase.name} was not exported`);
  }

  let result;
  try {
    result = fn(...testCase.args);
  } catch (error) {
    throw new Error(`${testCase.name}: unexpected trap: ${error.message}`);
  }
  const actual = BigInt.asUintN(64, result);
  if (actual !== testCase.expected) {
    throw new Error(`${testCase.name}: expected ${testCase.expected}, got ${actual}`);
  }
}

function runRejected(testCase) {
  const out = path.join(outDir, `${testCase.name}.wasm`);
  const compiled = compile(testCase.name, out);
  if (compiled.status === 0) {
    throw new Error(`${testCase.name} compiled but should have failed`);
  }

  const output = `${compiled.stdout}\n${compiled.stderr}`;
  if (!output.includes(testCase.message)) {
    throw new Error(`${testCase.name}: expected rejection containing "${testCase.message}"`);
  }
}

async function runTrapped(testCase) {
  const out = path.join(outDir, `${testCase.name}.wasm`);
  const compiled = compile(testCase.name, out);
  if (compiled.status !== 0) {
    throw new Error(`${testCase.name} failed to compile: ${compiled.stderr.trim()}`);
  }

  const wasm = fs.readFileSync(out);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const fn = instance.exports[testCase.name];
  if (typeof fn !== "function") {
    throw new Error(`${testCase.name} was not exported`);
  }

  let trapped = false;
  try {
    fn(...testCase.args);
  } catch (_error) {
    trapped = true;
  }
  if (!trapped) {
    throw new Error(`${testCase.name}: expected Wasm trap`);
  }
}

async function main() {
  fs.mkdirSync(outDir, { recursive: true });

  for (const testCase of accepted) {
    await runAccepted(testCase);
  }

  for (const testCase of rejected) {
    runRejected(testCase);
  }

  for (const testCase of trapped) {
    await runTrapped(testCase);
  }

  process.stdout.write(
    `checked ${accepted.length} accepted, ${rejected.length} rejected, and ${trapped.length} trapped cases\n`
  );
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
