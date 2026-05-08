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
  { name: "natDivModNormal", args: [7n], expected: 21n },
  { name: "natDivModNormal", args: [8n], expected: 22n },
  { name: "natDivModZero", args: [7n], expected: 7n },
  { name: "natSuccPred", args: [5n], expected: 10n },
  { name: "natSuccPred", args: [0n], expected: 1n },
  { name: "bitwiseOrXor", args: [], expected: 6n },
  { name: "bitwiseNotation", args: [], expected: 6n },
  { name: "complementNotation", args: [], expected: 255n },
  { name: "u8Complement", args: [], expected: 255n },
  { name: "shiftMasking", args: [], expected: 42n },
  { name: "shiftNotation", args: [], expected: 42n },
  { name: "uint8ShiftNotation", args: [], expected: 184n },
  { name: "uint8DirectShift", args: [], expected: 2255n },
  { name: "uint64OfNatValue", args: [41n], expected: 42n },
  { name: "uint64OfHugeNat", args: [], expected: 0n },
  { name: "natToUInt64Value", args: [41n], expected: 42n },
  { name: "natToUInt64Huge", args: [], expected: 0n },
  { name: "uint64ToNatValue", args: [41n], expected: 42n },
  { name: "uint64ToNatMethodMax", args: [], expected: 18446744073709551615n },
  { name: "wrappedUInt8Literal", args: [], expected: 44n },
  { name: "uint64ToUInt8Wrap", args: [], expected: 44n },
  { name: "uint8ToUInt64Value", args: [], expected: 256n },
  { name: "wrappedUInt32Literal", args: [], expected: 0n },
  { name: "uint32AddWrap", args: [], expected: 0n },
  { name: "uint32BitwiseShift", args: [], expected: 24n },
  { name: "uint32Complement", args: [], expected: 4294967295n },
  { name: "uint32MinMax", args: [], expected: 4000000030n },
  { name: "uint32Comparisons", args: [], expected: 1n },
  { name: "uint32DivMod", args: [], expected: 13333333331n },
  { name: "uint32DivModZero", args: [], expected: 7n },
  { name: "uint32ToUInt64Value", args: [], expected: 4294967296n },
  { name: "uint64ToUInt32Wrap", args: [], expected: 1n },
  { name: "uint8ToUInt32Value", args: [], expected: 256n },
  { name: "uint32ToUInt8Wrap", args: [], expected: 44n },
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
  { name: "productMatchDestructure", args: [], expected: 12n },
  { name: "productMatchUsesFirstOnly", args: [], expected: 7n },
  { name: "productMatchCondition", args: [], expected: 1n },
  { name: "productMatchNested", args: [], expected: 23n },
  { name: "productHelperResult", args: [], expected: 45n },
  { name: "productHelperParamSkipsTrap", args: [], expected: 7n },
  { name: "unitProductSecond", args: [], expected: 7n },
  { name: "unitHelperCall", args: [], expected: 11n },
  { name: "unitResultIgnored", args: [], expected: 12n },
  { name: "idRunLet", args: [], expected: 2n },
  { name: "idRunSkipsUnusedLetTrap", args: [], expected: 7n },
  { name: "idRunCondition", args: [], expected: 1n },
  { name: "idRunBind", args: [], expected: 2n },
  { name: "idRunBindSkipsUnusedTrap", args: [], expected: 7n },
  { name: "idRunBindProduct", args: [], expected: 12n },
  { name: "idRunBindOption", args: [], expected: 5n },
  { name: "idRunBindExcept", args: [], expected: 6n },
  { name: "idRunMut", args: [], expected: 2n },
  { name: "arrayUpdateRead", args: [], expected: 110n },
  { name: "arraySizeAfterSet", args: [], expected: 3n },
  { name: "arrayModifyInBounds", args: [], expected: 507n },
  { name: "arrayModifyOutOfBoundsSkipsFunctionTrap", args: [], expected: 7n },
  { name: "arrayInsertIdxIfInBoundsMiddle", args: [], expected: 1233n },
  { name: "arrayInsertIdxIfInBoundsEnd", args: [], expected: 459n },
  { name: "arrayInsertIdxIfInBoundsSkipsValueTrap", args: [], expected: 7n },
  { name: "arrayEraseIdxIfInBoundsMiddle", args: [], expected: 132n },
  { name: "arrayEraseIdxIfInBoundsLast", args: [], expected: 45n },
  { name: "arrayEraseIdxIfInBoundsOutOfBounds", args: [], expected: 78n },
  { name: "arrayPushRead", args: [], expected: 507n },
  { name: "nonzeroReplicateRead", args: [], expected: 77n },
  { name: "arrayPopRead", args: [], expected: 44n },
  { name: "arrayAppendRead", args: [], expected: 11223344n },
  { name: "arrayAppendEmptySides", args: [], expected: 7878n },
  { name: "arrayAppendNotationRead", args: [], expected: 1234n },
  { name: "arrayExtractRead", args: [], expected: 230n },
  { name: "arrayExtractClamps", args: [], expected: 340n },
  { name: "arrayLiteralRead", args: [], expected: 1030n },
  { name: "arrayGetProof", args: [], expected: 10n },
  { name: "arrayEmptyLiteral", args: [], expected: 1n },
  { name: "arrayEmptyConstructors", args: [], expected: 1n },
  { name: "arrayEmptyCapacitySkipsTrap", args: [], expected: 1n },
  { name: "arraySingletonRead", args: [], expected: 42n },
  { name: "arrayIsEmptyValues", args: [], expected: 1n },
  { name: "arrayBackRead", args: [], expected: 9n },
  { name: "arrayBackQuestionRead", args: [], expected: 9n },
  { name: "arrayBackQuestionEmpty", args: [], expected: 7n },
  { name: "arrayGetDRead", args: [1n], expected: 7n },
  { name: "arrayGetDRead", args: [2n], expected: 99n },
  { name: "arrayGetDSkipsDefaultTrap", args: [], expected: 5n },
  { name: "arrayGetQuestionRead", args: [1n], expected: 8n },
  { name: "arrayGetQuestionRead", args: [2n], expected: 99n },
  { name: "arrayGetQuestionGetDSkipsDefaultTrap", args: [], expected: 5n },
  { name: "arrayGetQuestionNoneSkipsPayloadTrap", args: [], expected: 5n },
  { name: "productArrayAlias", args: [], expected: 2211n },
  { name: "recLetDemo", args: [], expected: 518n },
  { name: "recExitDemo", args: [], expected: 314n },
  { name: "recThenBranchExitDemo", args: [], expected: 13n },
  { name: "recThenBranchFuelDemo", args: [], expected: 2n },
  { name: "recProductDemo", args: [], expected: 10n },
  { name: "recursiveDemandedFuelGet", args: [], expected: 7n },
  { name: "optionSomeMatch", args: [], expected: 8n },
  { name: "optionSomeFirstMatch", args: [], expected: 8n },
  { name: "optionNoneMatchSkipsSomeArm", args: [], expected: 5n },
  { name: "optionSomeMatchSkipsUnusedPayload", args: [], expected: 9n },
  { name: "optionLet", args: [], expected: 18n },
  { name: "optionBranch", args: [0n], expected: 11n },
  { name: "optionBranch", args: [1n], expected: 34n },
  { name: "optionHelperResult", args: [], expected: 6n },
  { name: "optionHelperNone", args: [], expected: 9n },
  { name: "optionHelperParam", args: [], expected: 3n },
  { name: "exceptOkMatch", args: [], expected: 8n },
  { name: "exceptOkFirstMatch", args: [], expected: 8n },
  { name: "exceptErrorMatch", args: [], expected: 14n },
  { name: "exceptErrorSkipsUnusedPayloadTrap", args: [], expected: 7n },
  { name: "exceptMatchCondition", args: [], expected: 1n },
  { name: "exceptProductPayload", args: [], expected: 12n },
  { name: "exceptMapOk", args: [], expected: 6n },
  { name: "exceptMapErrorSkipsFunctionTrap", args: [], expected: 7n },
  { name: "exceptMapProduct", args: [], expected: 12n },
  { name: "exceptMapError", args: [], expected: 6n },
  { name: "exceptMapErrorOkSkipsFunctionTrap", args: [], expected: 7n },
  { name: "exceptMapErrorProduct", args: [], expected: 12n },
  { name: "exceptBindOk", args: [], expected: 6n },
  { name: "exceptBindErrorSkipsFunctionTrap", args: [], expected: 7n },
  { name: "exceptBindFunctionError", args: [], expected: 9n },
  { name: "exceptBindProduct", args: [], expected: 12n },
  { name: "exceptHelperResult", args: [], expected: 6n },
  { name: "exceptHelperError", args: [], expected: 9n },
  { name: "exceptHelperParam", args: [], expected: 4n },
  { name: "exceptToOptionOk", args: [], expected: 6n },
  { name: "exceptToOptionErrorSkipsPayloadTrap", args: [], expected: 1n },
  { name: "exceptIsOkOkSkipsPayloadTrap", args: [], expected: 1n },
  { name: "exceptIsOkError", args: [], expected: 1n },
  { name: "exceptIsOkAsBool", args: [], expected: 1n },
  { name: "exceptOrElseError", args: [], expected: 5n },
  { name: "exceptOrElseOkSkipsFallbackTrap", args: [], expected: 5n },
  { name: "exceptOrElseFallbackError", args: [], expected: 9n },
  { name: "optionGetDNone", args: [], expected: 7n },
  { name: "optionGetDSomeSkipsDefaultTrap", args: [], expected: 5n },
  { name: "optionGetDProduct", args: [], expected: 12n },
  { name: "optionGetBangSome", args: [], expected: 6n },
  { name: "optionGetBangProduct", args: [], expected: 12n },
  { name: "optionGetBangCondition", args: [], expected: 1n },
  { name: "optionOrElseNone", args: [], expected: 7n },
  { name: "optionOrElseDirectSomeSkipsFallbackTrap", args: [], expected: 5n },
  { name: "optionOrElseProduct", args: [], expected: 12n },
  { name: "optionIsSomeSkipsPayloadTrap", args: [], expected: 1n },
  { name: "optionIsNoneValues", args: [], expected: 7n },
  { name: "optionElimSomeSkipsDefaultTrap", args: [], expected: 6n },
  { name: "optionElimNoneSkipsSomeArmTrap", args: [], expected: 7n },
  { name: "optionElimProduct", args: [], expected: 12n },
  { name: "optionMapSome", args: [], expected: 6n },
  { name: "optionMapNoneSkipsFunctionTrap", args: [], expected: 7n },
  { name: "optionMapProduct", args: [], expected: 12n },
  { name: "optionFilterSomeKeep", args: [], expected: 5n },
  { name: "optionFilterSomeDrop", args: [], expected: 1n },
  { name: "optionFilterNoneSkipsPredicateTrap", args: [], expected: 7n },
  { name: "optionFilterIgnoresPayloadTrap", args: [], expected: 1n },
  { name: "optionAnySome", args: [], expected: 1n },
  { name: "optionAnyNoneSkipsPredicateTrap", args: [], expected: 7n },
  { name: "optionAllSomeFalse", args: [], expected: 7n },
  { name: "optionAllNoneSkipsPredicateTrap", args: [], expected: 7n },
  { name: "optionBindSome", args: [], expected: 6n },
  { name: "optionBindNoneSkipsFunctionTrap", args: [], expected: 7n },
  { name: "optionBindFunctionNone", args: [], expected: 9n },
  { name: "optionBindProduct", args: [], expected: 12n },
  { name: "natComparisons", args: [2n], expected: 10n },
  { name: "natComparisons", args: [3n], expected: 20n },
  { name: "natComparisons", args: [6n], expected: 30n },
  { name: "natBoolComparisons", args: [2n], expected: 10n },
  { name: "natBoolComparisons", args: [3n], expected: 20n },
  { name: "natBoolComparisons", args: [6n], expected: 30n },
  { name: "natBltAsBool", args: [2n], expected: 1n },
  { name: "natBltAsBool", args: [3n], expected: 0n },
  { name: "natBeqAsBool", args: [3n], expected: 1n },
  { name: "natBeqAsBool", args: [4n], expected: 0n },
  { name: "natBeqCondition", args: [3n], expected: 1n },
  { name: "natBeqCondition", args: [4n], expected: 2n },
  { name: "u64Comparisons", args: [2n], expected: 10n },
  { name: "u64Comparisons", args: [3n], expected: 20n },
  { name: "u64Comparisons", args: [6n], expected: 30n },
  { name: "greaterComparisons", args: [2n], expected: 10n },
  { name: "greaterComparisons", args: [3n], expected: 20n },
  { name: "greaterComparisons", args: [6n], expected: 30n },
  { name: "bneScalars", args: [2n], expected: 1n },
  { name: "bneScalars", args: [3n], expected: 2n },
  { name: "bneAsBool", args: [2n], expected: 1n },
  { name: "bneAsBool", args: [3n], expected: 0n },
  { name: "bneBool", args: [], expected: 1n },
  { name: "boolXorValues", args: [0n, 0n], expected: 0n },
  { name: "boolXorValues", args: [0n, 1n], expected: 1n },
  { name: "boolXorValues", args: [1n, 1n], expected: 0n },
  { name: "boolToNatValue", args: [0n], expected: 1n },
  { name: "boolToNatValue", args: [1n], expected: 2n },
  { name: "boolMatchScalar", args: [0n], expected: 10n },
  { name: "boolMatchScalar", args: [1n], expected: 20n },
  { name: "boolMatchTrueFirstScalar", args: [0n], expected: 10n },
  { name: "boolMatchTrueFirstScalar", args: [1n], expected: 20n },
  { name: "boolMatchTrueFirstSkipsFalseTrap", args: [], expected: 7n },
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
  { name: "dependentIfNat", args: [2n], expected: 1n },
  { name: "dependentIfNat", args: [3n], expected: 2n },
  { name: "dependentIfSkipsElseTrap", args: [], expected: 7n },
  { name: "dependentIfSkipsThenTrap", args: [], expected: 8n },
  { name: "dependentIfProduct", args: [2n], expected: 12n },
  { name: "dependentIfProduct", args: [3n], expected: 34n },
  { name: "natMatchZero", args: [0n], expected: 10n },
  { name: "natMatchZero", args: [3n], expected: 20n },
  { name: "natMatchSuccFirst", args: [0n], expected: 10n },
  { name: "natMatchSuccFirst", args: [3n], expected: 32n },
  { name: "natMatchZeroSkipsSuccTrap", args: [], expected: 7n },
  { name: "natMatchSuccSkipsZeroTrap", args: [], expected: 1n },
  { name: "natMatchBoolCondition", args: [0n], expected: 1n },
  { name: "natMatchBoolCondition", args: [3n], expected: 2n },
  { name: "natMatchProduct", args: [0n], expected: 12n },
  { name: "natMatchProduct", args: [3n], expected: 29n },
  { name: "natMinMax", args: [7n, 3n], expected: 37n },
  { name: "natMinMax", args: [2n, 9n], expected: 29n },
  { name: "u64MinMax", args: [7n, 3n], expected: 37n },
  { name: "u64MinMax", args: [2n, 9n], expected: 29n },
  { name: "u8MinMax", args: [], expected: 280n },
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
    name: "rejectExceptReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectExceptReturn",
  },
  {
    name: "rejectExceptParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectExceptParam",
  },
  {
    name: "rejectExceptUnitError",
    message: "unsupported Except.ok application",
  },
  {
    name: "rejectUnitReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUnitReturn",
  },
  {
    name: "rejectUnitParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUnitParam",
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
    name: "rejectUInt32Param",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUInt32Param",
  },
  {
    name: "rejectUInt32Return",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUInt32Return",
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
  {
    name: "rejectIdForLoop",
    message: "unsupported expression: fun",
  },
];

const trapped = [
  { name: "natAddOverflow", args: [] },
  { name: "natMulOverflow", args: [] },
  { name: "natSuccOverflow", args: [] },
  { name: "optionGetBangNoneTrap", args: [] },
  { name: "arrayBackEmptyTrap", args: [] },
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
