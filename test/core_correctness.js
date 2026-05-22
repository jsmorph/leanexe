#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");
const host = require("./wasmtime_host");
const {
  HostPlan,
  SparseMemory,
  arrayLayout,
  byteArrayLayout,
  checkMemoryExpectations,
  materializeArgPlan,
  memoryReadCommands,
  scalarLayout,
  structLayout,
  variantLayout,
} = require("../tools/abi_layout");

const moduleName = "LeanExe.Examples.Correctness";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const wasmtime = process.env.WASMTIME || path.join("build", "tools", "wasmtime", "current", "wasmtime");
const outDir = path.join(".lake", "build", "core-correctness");

const watSizeGuards = [
  { name: "arrayStructureReplicateHelperRead", maxBytes: 500_000 },
];

const u64Layout = scalarLayout("UInt64");
const u64ArrayLayout = arrayLayout(u64Layout);
const byteArrayArrayLayout = arrayLayout(byteArrayLayout);
const nestedU64ArrayLayout = arrayLayout(u64ArrayLayout);
const optionArrayByteArrayLayout = variantLayout([[], [byteArrayArrayLayout]]);
const exceptByteArrayArrayLayout = variantLayout([[byteArrayLayout], [byteArrayArrayLayout]]);
const optionByteArrayLayout = variantLayout([[], [byteArrayLayout]]);
const exceptByteArrayByteArrayLayout = variantLayout([[byteArrayLayout], [byteArrayLayout]]);
const tokenLayout = variantLayout([[byteArrayLayout], [u64Layout]]);
const optionByteArrayArrayLayout = arrayLayout(optionByteArrayLayout);
const exceptByteArrayByteArrayArrayLayout = arrayLayout(exceptByteArrayByteArrayLayout);
const tokenArrayLayout = arrayLayout(tokenLayout);
const byteOutputStateLayout = structLayout([
  ["count", u64Layout],
  ["bytes", byteArrayLayout],
]);
const byteOutputStateArrayLayout = arrayLayout(byteOutputStateLayout);
const arrayBoxLayout = structLayout([
  ["values", u64ArrayLayout],
  ["count", u64Layout],
]);
const arrayBoxArrayLayout = arrayLayout(arrayBoxLayout);
const byteArrayGroupLayout = structLayout([
  ["values", byteArrayArrayLayout],
  ["marker", u64Layout],
]);
const byteArrayGroupArrayLayout = arrayLayout(byteArrayGroupLayout);
const heapArrayResultLayout = variantLayout([[byteArrayLayout], [byteArrayArrayLayout, u64Layout]]);
const optionArrayOptionByteArrayLayout = variantLayout([[], [optionByteArrayArrayLayout]]);

const optionByteArrayArraySample = [
  { tag: 1, fields: [[65]] },
  { tag: 0, fields: [] },
  { tag: 1, fields: [[66, 67]] },
];
const exceptByteArrayByteArrayArraySample = [
  { tag: 1, fields: [[65]] },
  { tag: 0, fields: [[66, 67]] },
  { tag: 1, fields: [[68, 69, 70]] },
];
const publicTokenArraySample = [
  { tag: 0, fields: [[65]] },
  { tag: 1, fields: [7n] },
  { tag: 0, fields: [[66, 67]] },
];
const byteArrayGroupArraySample = [
  { values: [[65], [66, 67]], marker: 2n },
  { values: [[68]], marker: 3n },
];

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
  { name: "uint8ParamToNat", args: [300n], expected: 44n },
  { name: "uint8Return", args: [], expected: 44n },
  { name: "uint8AddWrap", args: [], expected: 0n },
  { name: "uint8SubWrap", args: [], expected: 255n },
  { name: "uint8MulWrap", args: [], expected: 16n },
  { name: "uint8DivModZero", args: [], expected: 7n },
  { name: "uint32ParamToNat", args: [4294967297n], expected: 1n },
  { name: "uint32Return", args: [], expected: 1n },
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
  { name: "productEquality", args: [], expected: 1n },
  { name: "productInequality", args: [], expected: 1n },
  { name: "productEqualityShortCircuit", args: [], expected: 1n },
  { name: "structureProjection", args: [], expected: 7n },
  { name: "structureUpdateProjection", args: [], expected: 19n },
  { name: "structureHelperResult", args: [], expected: 56n },
  { name: "structureEquality", args: [], expected: 1n },
  { name: "structureInequality", args: [], expected: 1n },
  { name: "nestedStructureEquality", args: [], expected: 1n },
  { name: "structureEqualityShortCircuit", args: [], expected: 1n },
  { name: "structurePropEquality", args: [], expected: 1n },
  { name: "structureReturn", args: [4n], expected: [5n, 6n] },
  { name: "structureBranchReturn", args: [0n], expected: [1n, 2n] },
  { name: "structureBranchReturn", args: [1n], expected: [3n, 4n] },
  { name: "nestedStructureReturn", args: [], expected: [1n, 2n, 3n] },
  {
    name: "structureArrayReturn",
    args: [],
    expected: [null, 2n],
    memoryArrays: [{ resultIndex: 0, values: [4n, 5n] }],
  },
  {
    name: "structurePointArrayReturn",
    args: [],
    expected: [null, 2n],
    memoryArrays: [{ resultIndex: 0, length: 2, values: [1n, 2n, 3n, 4n] }],
  },
  { name: "structureParam", args: [2n, 3n], expected: 23n },
  { name: "structureCallArgMaterialized", args: [], expected: 89n },
  { name: "structureMatchDestructure", args: [], expected: 12n },
  { name: "structureMatchUsesFirstOnly", args: [], expected: 7n },
  { name: "structureMatchCondition", args: [], expected: 1n },
  { name: "proofStructureProjection", args: [], expected: 10n },
  { name: "proofStructureReturn", args: [], expected: 9n },
  { name: "proofStructureParam", args: [8n], expected: 9n },
  { name: "proofStructureMatch", args: [], expected: 8n },
  { name: "paramBoxProjection", args: [], expected: 42n },
  { name: "paramBoxMatch", args: [], expected: 8n },
  { name: "paramPairBoxParam", args: [9n, 1n], expected: 9n },
  { name: "paramPairBoxParam", args: [9n, 0n], expected: 0n },
  { name: "paramBoxReturn", args: [4n], expected: 5n },
  { name: "paramCheckedBoxProjection", args: [], expected: 9n },
  { name: "paramBoxArrayFold", args: [], expected: 5n },
  { name: "genericBoxHelperProjection", args: [], expected: 22n },
  { name: "genericPairBoxHelper", args: [], expected: 9n },
  { name: "genericBoxHelperSkipsUnusedTrap", args: [], expected: 7n },
  { name: "genericInterleavedLambdaHelper", args: [], expected: 22n },
  { name: "digitStateParserAllDigitsDemo", args: [], expected: 603n },
  { name: "digitStateParserStopsDemo", args: [], expected: 999n },
  { name: "statusOkMatch", args: [], expected: 8n },
  { name: "statusErrorMatch", args: [], expected: 9n },
  { name: "statusSourceOrderIndependentMatch", args: [], expected: 11n },
  { name: "statusSkipsUnusedPayloadTrap", args: [], expected: 7n },
  { name: "statusMatchCondition", args: [], expected: 1n },
  { name: "statusHelperResult", args: [], expected: 5n },
  { name: "statusBranchReturn", args: [0n], expected: [0n, 5n, 0n] },
  { name: "statusBranchReturn", args: [1n], expected: [1n, 0n, 9n] },
  { name: "statusParam", args: [0n, 5n, 0n], expected: 15n },
  { name: "statusParam", args: [1n, 0n, 7n], expected: 27n },
  { name: "modeMatch", args: [], expected: 2n },
  { name: "modeReturn", args: [0n], expected: 0n },
  { name: "modeReturn", args: [1n], expected: 2n },
  { name: "checkedStatusMatch", args: [], expected: 8n },
  { name: "checkedStatusReturn", args: [], expected: [0n, 9n, 0n] },
  { name: "paramResultOkMatch", args: [], expected: 6n },
  { name: "paramResultErrorMatch", args: [], expected: 14n },
  { name: "paramResultReturn", args: [0n], expected: [0n, 7n, 0n, 0n] },
  { name: "paramResultReturn", args: [3n], expected: [1n, 0n, 3n, 4n] },
  { name: "paramResultParam", args: [0n, 5n, 0n, 0n], expected: 5n },
  { name: "paramResultParam", args: [1n, 0n, 2n, 3n], expected: 23n },
  { name: "checkedPayloadMatch", args: [], expected: 10n },
  { name: "paramResultArrayFold", args: [], expected: 75n },
  { name: "genericResultIsOkDemo", args: [], expected: 1n },
  { name: "genericResultValueOrDemo", args: [], expected: 34n },
  { name: "genericCheckedPayloadDemo", args: [], expected: 12n },
  { name: "inductiveEqualitySameCtor", args: [], expected: 1n },
  { name: "inductiveInequalitySameCtor", args: [], expected: 1n },
  { name: "inductiveEqualityDifferentCtor", args: [], expected: 1n },
  { name: "inductiveEqualityDifferentCtorSkipsPayload", args: [], expected: 1n },
  { name: "inductivePropEquality", args: [], expected: 1n },
  { name: "optionStructuralEquality", args: [], expected: 1n },
  { name: "byteArrayEquality", args: [], expected: 1n },
  { name: "byteArrayInequalityValue", args: [], expected: 1n },
  { name: "byteArrayInequalityLength", args: [], expected: 1n },
  { name: "byteArrayFieldStructureEquality", args: [], expected: 1n },
  { name: "byteArrayOptionEquality", args: [], expected: 1n },
  { name: "arrayEquality", args: [], expected: 1n },
  { name: "arrayInequalityValue", args: [], expected: 1n },
  { name: "arrayInequalityLength", args: [], expected: 1n },
  { name: "arrayPropEquality", args: [], expected: 1n },
  { name: "pointArrayEquality", args: [], expected: 1n },
  { name: "statusArrayEquality", args: [], expected: 1n },
  { name: "nestedArrayEquality", args: [], expected: 1n },
  { name: "byteArrayArrayEquality", args: [], expected: 1n },
  { name: "byteArrayStructureArrayEquality", args: [], expected: 1n },
  { name: "optionReturn", args: [0n], expected: [0n, 0n] },
  { name: "optionReturn", args: [3n], expected: [1n, 7n] },
  { name: "optionPointReturn", args: [0n], expected: [0n, 0n, 0n] },
  { name: "optionPointReturn", args: [5n], expected: [1n, 5n, 6n] },
  { name: "optionParam", args: [0n, 44n], expected: 0n },
  { name: "optionParam", args: [1n, 5n], expected: 5n },
  { name: "optionPointParam", args: [0n, 9n, 9n], expected: 0n },
  { name: "optionPointParam", args: [1n, 3n, 4n], expected: 7n },
  { name: "exceptReturn", args: [0n], expected: [0n, 7n, 0n] },
  { name: "exceptReturn", args: [3n], expected: [1n, 0n, 7n] },
  { name: "exceptPointReturn", args: [0n], expected: [0n, 7n, 0n, 0n] },
  { name: "exceptPointReturn", args: [5n], expected: [1n, 0n, 5n, 6n] },
  { name: "exceptParam", args: [0n, 7n, 0n], expected: 7n },
  { name: "exceptParam", args: [1n, 0n, 5n], expected: 5n },
  {
    name: "byteArrayReturnABC",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 67] }],
  },
  { name: "byteArrayPushSize", args: [], expected: 3n },
  {
    name: "byteArrayAppendReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 67] }],
  },
  { name: "byteArrayAppendSize", args: [], expected: 3n },
  {
    name: "byteArraySetReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 90, 67] }],
  },
  { name: "byteArraySetSize", args: [], expected: 3n },
  {
    name: "byteArraySetBangReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 90] }],
  },
  { name: "byteArrayToUInt64LE", args: [], expected: 578437695752307201n },
  { name: "byteArrayToUInt64BE", args: [], expected: 72623859790382856n },
  {
    name: "byteArrayMkReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 67] }],
  },
  { name: "byteArrayMkSize", args: [], expected: 3n },
  {
    name: "byteArrayStringLiteralReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 67] }],
  },
  { name: "byteArrayStringLiteralSize", args: [], expected: 3n },
  {
    name: "byteArrayStringAppendReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 67] }],
  },
  {
    name: "byteArrayStringLetReturn",
    args: [],
    expected: [null, 2n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 90] }],
  },
  {
    name: "byteArrayStringConstReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [88, 89, 90] }],
  },
  { name: "stringLengthAppend", args: [], expected: 4n },
  { name: "stringIsEmptyLet", args: [], expected: 1n },
  { name: "stringEqualityLet", args: [], expected: 1n },
  { name: "stringInequalityLet", args: [], expected: 1n },
  {
    name: "byteArrayBranchHelperReturn",
    args: [0n],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 67] }],
  },
  {
    name: "byteArrayBranchHelperReturn",
    args: [1n],
    expected: [null, 1n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [90] }],
  },
  {
    name: "byteArrayCopySliceReturn",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 89, 90] }],
  },
  { name: "byteArrayCopySliceSize", args: [], expected: 3n },
  {
    name: "byteArrayCopySliceShortSource",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 88, 67] }],
  },
  { name: "byteArrayCopySliceExactSkipsTrap", args: [], expected: 3n },
  { name: "byteArrayFoldSum", args: [], expected: 6n },
  { name: "byteArrayFoldWindow", args: [], expected: 23n },
  { name: "byteArrayFoldEmptySkipsFunctionTrap", args: [], expected: 7n },
  { name: "byteArrayFoldStructAccumulator", args: [], expected: 36n },
  { name: "byteArrayFoldProductAccumulator", args: [], expected: 211n },
  { name: "byteArrayFoldStatusAccumulator", args: [], expected: 24n },
  { name: "byteArrayFoldArrayAccumulator", args: [], expected: 12n },
  {
    name: "byteArrayFoldByteArrayAccumulator",
    args: [],
    expected: [null, 2n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [1, 2] }],
  },
  { name: "byteArrayFoldByteArrayAccumulatorReleaseStats", args: [], expected: 30202n },
  { name: "byteArrayFoldMExceptSuccess", args: [], expected: [1n, 0n, 6n] },
  { name: "byteArrayFoldMExceptErrorSkipsRestTrap", args: [], expected: [0n, 21n, 0n] },
  { name: "byteArrayFoldMOptionSuccess", args: [], expected: [1n, 6n] },
  { name: "byteArrayFoldMOptionNoneSkipsRestTrap", args: [], expected: [0n, 0n] },
  {
    name: "byteArrayFoldMOptionByteArray",
    args: [],
    expected: [1n, null, 2n],
    memoryBytes: [{ resultIndex: 1, lengthIndex: 2, values: [65, 66] }],
  },
  { name: "byteArrayArrayReadSize", args: [], expected: 12n },
  { name: "byteArrayArrayFoldSize", args: [], expected: 6n },
  {
    name: "byteArrayArrayFoldAppend",
    args: [],
    expected: [null, 6n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66, 67, 68, 69, 70] }],
  },
  { name: "byteArrayFieldStructureArrayFold", args: [], expected: 6n },
  { name: "byteArrayStructReplicateRuntimeReleaseFrees", args: [], expected: 202n },
  { name: "nestedArrayRuntimeReleaseFrees", args: [], expected: 202n },
  { name: "structArrayFieldRuntimeReleaseFrees", args: [], expected: 202n },
  { name: "optionByteArrayArrayRuntimeReleaseFrees", args: [], expected: 302n },
  { name: "publicTokenArrayRuntimeReleaseFrees", args: [], expected: 302n },
  { name: "byteArrayGroupArrayRuntimeReleaseFrees", args: [], expected: 403n },
  { name: "ownedArrayCallTempScalar", args: [], expected: 5n },
  { name: "ownedByteArrayCallTempScalar", args: [], expected: 66n },
  { name: "ownedArrayParamCallTempScalar", args: [], expected: 16n },
  { name: "ownedByteArrayParamCallTempScalar", args: [], expected: 100n },
  {
    name: "byteArrayResultDropsOwnedTemp",
    args: [],
    expected: [null, 1n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [66] }],
  },
  { name: "byteArrayResultDropsOwnedTempStats", args: [], expected: 10101n },
  { name: "ownedRecursiveNodeParamCallTempScalar", args: [], expected: 310n },
  { name: "unusedRecursiveRuntimeReleaseFrees", args: [], expected: 3n },
  { name: "arrayFoldRecursiveAccumulatorReleaseStats", args: [], expected: 30606n },
  { name: "recursiveScenarioRuntimeReleaseStats", args: [0n], expected: 101n },
  { name: "recursiveScenarioRuntimeReleaseStats", args: [1n], expected: 707n },
  { name: "recursiveScenarioRuntimeReleaseStats", args: [2n], expected: 707n },
  { name: "recursiveScenarioHelperRuntimeReleaseStats", args: [0n], expected: 101n },
  { name: "recursiveScenarioHelperRuntimeReleaseStats", args: [1n], expected: 707n },
  { name: "recursiveScenarioHelperRuntimeReleaseStats", args: [2n], expected: 707n },
  { name: "sharedRecursiveChildReleaseStats", args: [], expected: 10302n },
  { name: "ownedBoxCallTempScalar", args: [], expected: 13n },
  {
    name: "byteArrayFoldByteOutputState",
    args: [],
    expected: [3n, null, 3n],
    memoryBytes: [{ resultIndex: 1, lengthIndex: 2, values: [1, 2, 3] }],
  },
  { name: "byteArrayFindIdxSome", args: [], expected: [1n, 1n] },
  { name: "byteArrayFindIdxNone", args: [], expected: [0n, 0n] },
  { name: "byteArrayFindIdxStart", args: [], expected: [1n, 2n] },
  { name: "byteArrayFindIdxEmptySkipsPredicateTrap", args: [], expected: [0n, 0n] },
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
  { name: "idRunMutNestedIf", args: [], expected: 34n },
  { name: "idRunMutStructureReturn", args: [], expected: [5n, 2n] },
  {
    name: "idRunMutByteArrayReturn",
    args: [],
    expected: [null, 2n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66] }],
  },
  { name: "idRunMutOptionReturn", args: [], expected: [1n, 9n] },
  { name: "idRunMutExceptReturn", args: [], expected: [1n, 0n, 7n] },
  { name: "idRunMutOptionMatch", args: [], expected: 5n },
  { name: "idRunMutOptionIfLet", args: [], expected: 8n },
  { name: "idRunMutOptionCatchAllMatch", args: [], expected: 11n },
  { name: "idRunMutStatusMatchReturn", args: [], expected: [0n, 10n, 0n] },
  { name: "idRunMutStatusIfLet", args: [], expected: 7n },
  { name: "idRunMutStatusCatchAllMatch", args: [], expected: 29n },
  { name: "idRunMutModeIfLet", args: [], expected: 7n },
  { name: "idRunWhileStatusIfLetSum", args: [], expected: 15n },
  { name: "idRunMutMatchStateRecord", args: [], expected: [2n, 9n] },
  { name: "idRunByteArrayForSum", args: [], expected: 6n },
  { name: "idRunArrayForSum", args: [], expected: 6n },
  { name: "idRunArrayForTwoCounters", args: [], expected: 63n },
  { name: "idRunNestedArrayForSum", args: [], expected: 10n },
  { name: "idRunArrayForBreakSum", args: [], expected: 3n },
  { name: "idRunArrayForContinueNoElse", args: [], expected: 6n },
  { name: "idRunByteArrayForState", args: [], expected: [3n, 6n] },
  { name: "idRunByteArrayForBreakSum", args: [], expected: 3n },
  { name: "idRunByteArrayForContinueNoElse", args: [], expected: 6n },
  {
    name: "idRunByteArrayForOutput",
    args: [],
    expected: [null, 2n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [1, 2] }],
  },
  {
    name: "idRunByteArrayForOutputBreak",
    args: [],
    expected: [null, 2n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [1, 2] }],
  },
  {
    name: "idRunByteArrayForOutputContinue",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [1, 2, 3] }],
  },
  { name: "idRunByteArrayForOutputReleaseStats", args: [], expected: 30202n },
  { name: "idRunArrayForStatus", args: [], expected: [1n, 0n, 2n] },
  { name: "idRunArrayForStatusScore", args: [], expected: 102n },
  { name: "idRunRangeForCount", args: [], expected: 3n },
  { name: "idRunRangeForStepSum", args: [], expected: 9n },
  { name: "idRunRangeForState", args: [], expected: [3n, 9n] },
  { name: "idRunRangeForBreakSum", args: [], expected: 6n },
  { name: "idRunRangeForBreakNoElse", args: [], expected: 3n },
  { name: "idRunRangeForContinueNoElse", args: [], expected: 12n },
  {
    name: "idRunRangeForByteArrayOutput",
    args: [],
    expected: [null, 2n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [1, 1] }],
  },
  { name: "idRunRangeForByteArrayOutputReleaseStats", args: [], expected: 30202n },
  { name: "idRunRangeForBreakState", args: [], expected: [3n, 6n] },
  { name: "idRunRangeForContinueState", args: [], expected: [4n, 11n] },
  { name: "exceptForArraySum", args: [], expected: [1n, 0n, 6n] },
  { name: "exceptForArrayErrorSkipsRestTrap", args: [], expected: [0n, 21n, 0n] },
  { name: "optionForByteArraySum", args: [], expected: [1n, 6n] },
  { name: "optionForByteArrayNoneSkipsRestTrap", args: [], expected: [0n, 0n] },
  { name: "exceptForRangeBreakSum", args: [], expected: [1n, 0n, 6n] },
  { name: "optionForArrayContinueSum", args: [], expected: [1n, 4n] },
  { name: "optionWhileSum", args: [], expected: [1n, 3n] },
  {
    name: "optionForByteArrayOutput",
    args: [],
    expected: [1n, null, 3n],
    memoryBytes: [{ resultIndex: 1, lengthIndex: 2, values: [65, 66, 67] }],
  },
  { name: "optionForByteArrayOutputNoneSkipsRestTrap", args: [], expected: [0n, 0n, 0n] },
  {
    name: "exceptForByteArrayOutput",
    args: [],
    expected: [1n, 0n, null, 3n],
    memoryBytes: [{ resultIndex: 2, lengthIndex: 3, values: [65, 66, 67] }],
  },
  { name: "exceptForByteArrayOutputErrorSkipsRestTrap", args: [], expected: [0n, 21n, 0n, 0n] },
  {
    name: "optionForByteArrayState",
    args: [],
    expected: [1n, 3n, null, 3n],
    memoryBytes: [{ resultIndex: 2, lengthIndex: 3, values: [65, 66, 67] }],
  },
  { name: "optionForByteArrayOutputReleaseStats", args: [], expected: 10202n },
  { name: "exceptForByteArrayOutputReleaseStats", args: [], expected: 10202n },
  { name: "optionForByteArrayStateReleaseStats", args: [], expected: 30202n },
  { name: "idRunWhileSum", args: [], expected: 10n },
  { name: "idRunWhileBreakContinue", args: [], expected: 12n },
  { name: "idRunWhileState", args: [], expected: [4n, 6n] },
  { name: "idRunNestedWhileSum", args: [], expected: 63n },
  {
    name: "idRunWhileByteArrayOutput",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [1, 1, 1] }],
  },
  { name: "idRunWhileDigitScanner", args: [], expected: [2n, 103n] },
  {
    name: "idRunWhileDigitOutput",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [1, 2, 3] }],
  },
  { name: "idRunWhileParserExcept", args: [], expected: [0n, 2n, 0n, 0n] },
  { name: "idRunWhileArrayUpdateSum", args: [], expected: 9n },
  {
    name: "idRunWhileParserBufferState",
    args: [],
    expected: [2n, null, 2n, 0n],
    memoryBytes: [{ resultIndex: 1, lengthIndex: 2, values: [1, 2] }],
  },
  {
    name: "idRunWhileArrayBuilderState",
    args: [],
    expected: [null, 3n],
    memoryArrays: [{ resultIndex: 0, values: [1n, 3n, 5n] }],
  },
  { name: "exceptDoStateFromLoop", args: [], expected: [1n, 0n, 4n, 16n] },
  { name: "exceptDoLoopErrorSkipsRestTrap", args: [], expected: 1n },
  {
    name: "exceptDoByteArrayFromValidation",
    args: [],
    expected: [1n, 0n, null, 2n],
    memoryBytes: [{ resultIndex: 2, lengthIndex: 3, values: [4, 5] }],
  },
  { name: "exceptDoStatusFromLoop", args: [], expected: [1n, 0n, 0n, 7n, 0n] },
  { name: "idFunctionUInt64", args: [4n], expected: 5n },
  { name: "idFunctionProductSecond", args: [], expected: 7n },
  { name: "arrayUpdateRead", args: [], expected: 110n },
  { name: "arraySizeAfterSet", args: [], expected: 3n },
  { name: "arrayProofSetRead", args: [], expected: 19n },
  { name: "arraySetIfInBoundsRead", args: [], expected: 19n },
  { name: "arraySetIfInBoundsSkipsValueTrap", args: [], expected: 7n },
  { name: "arrayModifyInBounds", args: [], expected: 507n },
  { name: "arrayModifyOutOfBoundsSkipsFunctionTrap", args: [], expected: 7n },
  { name: "arrayInsertIdxIfInBoundsMiddle", args: [], expected: 1233n },
  { name: "arrayInsertIdxIfInBoundsEnd", args: [], expected: 459n },
  { name: "arrayInsertIdxIfInBoundsSkipsValueTrap", args: [], expected: 7n },
  { name: "arrayEraseIdxIfInBoundsMiddle", args: [], expected: 132n },
  { name: "arrayEraseIdxIfInBoundsLast", args: [], expected: 45n },
  { name: "arrayEraseIdxIfInBoundsOutOfBounds", args: [], expected: 78n },
  { name: "arraySwapIfInBoundsEnds", args: [], expected: 4231n },
  { name: "arraySwapIfInBoundsSameIndex", args: [], expected: 56n },
  { name: "arraySwapIfInBoundsOutOfBounds", args: [], expected: 789n },
  { name: "arrayReverseRead", args: [], expected: 321n },
  { name: "arrayReverseSmall", args: [], expected: 7n },
  { name: "arrayProofInsertIdxRead", args: [], expected: 123n },
  { name: "arrayInsertIdxBangRead", args: [], expected: 123n },
  { name: "arrayProofEraseIdxRead", args: [], expected: 13n },
  { name: "arrayEraseIdxBangRead", args: [], expected: 13n },
  { name: "arrayProofSwapRead", args: [], expected: 321n },
  { name: "arraySwapAtRead", args: [], expected: 209n },
  { name: "arraySwapAtFirstSkipsValueTrap", args: [], expected: 2n },
  { name: "arraySwapAtLetFirstSkipsValueTrap", args: [], expected: 2n },
  { name: "arrayPushRead", args: [], expected: 507n },
  { name: "nonzeroReplicateRead", args: [], expected: 77n },
  { name: "arrayPopRead", args: [], expected: 44n },
  { name: "arrayAppendRead", args: [], expected: 11223344n },
  { name: "arrayAppendEmptySides", args: [], expected: 7878n },
  { name: "arrayAppendNotationRead", args: [], expected: 1234n },
  { name: "arrayExtractRead", args: [], expected: 230n },
  { name: "arrayExtractClamps", args: [], expected: 340n },
  { name: "arrayMapRead", args: [], expected: 246n },
  { name: "arrayMapAliasRead", args: [], expected: 111n },
  { name: "arrayMapEmptySkipsFunctionTrap", args: [], expected: 0n },
  { name: "arrayFoldSum", args: [], expected: 6n },
  { name: "arrayFoldWindow", args: [], expected: 23n },
  { name: "arrayFoldEmptySkipsFunctionTrap", args: [], expected: 7n },
  { name: "arrayFoldrDigits", args: [], expected: 321n },
  { name: "arrayFoldrWindow", args: [], expected: 32n },
  { name: "arrayFoldrStartClamps", args: [], expected: 321n },
  { name: "arrayFoldrEmptySkipsFunctionTrap", args: [], expected: 7n },
  { name: "arrayFoldrStructAccumulator", args: [], expected: 3321n },
  {
    name: "arrayFoldrByteArrayAccumulator",
    args: [],
    expected: [null, 3n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [67, 66, 65] }],
  },
  { name: "arrayFoldrByteArrayAccumulatorReleaseStats", args: [], expected: 30202n },
  { name: "arrayFoldStructAccumulator", args: [], expected: 36n },
  { name: "arrayFoldProductAccumulator", args: [], expected: 39n },
  { name: "arrayFoldStatusAccumulator", args: [], expected: 6n },
  { name: "arrayFoldArrayAccumulator", args: [], expected: 1113n },
  {
    name: "arrayFoldByteArrayAccumulator",
    args: [],
    expected: [null, 2n],
    memoryBytes: [{ resultIndex: 0, lengthIndex: 1, values: [65, 66] }],
  },
  { name: "arrayFoldByteArrayAccumulatorReleaseStats", args: [], expected: 30202n },
  { name: "arrayFoldOptionByteArrayAccumulatorReleaseStats", args: [], expected: 30502n },
  { name: "arrayFoldPublicTokenAccumulatorReleaseStats", args: [], expected: 30402n },
  { name: "arrayFoldByteArrayGroupAccumulatorReleaseStats", args: [], expected: 30502n },
  { name: "arrayFoldMExceptSuccess", args: [], expected: [1n, 0n, 6n] },
  { name: "arrayFoldMExceptErrorSkipsRestTrap", args: [], expected: [0n, 21n, 0n] },
  { name: "arrayFoldMOptionSuccess", args: [], expected: [1n, 6n] },
  { name: "arrayFoldMOptionNoneSkipsRestTrap", args: [], expected: [0n, 0n] },
  { name: "arrayAttachFoldMExcept", args: [], expected: [1n, 0n, 6n] },
  {
    name: "arrayFoldByteOutputState",
    args: [],
    expected: [3n, null, 3n],
    memoryBytes: [{ resultIndex: 1, lengthIndex: 2, values: [65, 66, 67] }],
  },
  { name: "arrayFindIdxSome", args: [], expected: [1n, 1n] },
  { name: "arrayFindIdxNone", args: [], expected: [0n, 0n] },
  { name: "arrayFindIdxStructure", args: [], expected: [1n, 1n] },
  { name: "arrayFindIdxStatus", args: [], expected: [1n, 1n] },
  { name: "arrayFindIdxEmptySkipsPredicateTrap", args: [], expected: [0n, 0n] },
  { name: "arrayFindSome", args: [], expected: [1n, 2n] },
  { name: "arrayFindNone", args: [], expected: [0n, 0n] },
  { name: "arrayFindStructure", args: [], expected: [1n, 3n, 4n] },
  { name: "arrayFindStatus", args: [], expected: [1n, 0n, 7n, 0n] },
  { name: "arrayFindEmptySkipsPredicateTrap", args: [], expected: [0n, 0n] },
  { name: "arrayAnySome", args: [], expected: 1n },
  { name: "arrayAnyWindowFalse", args: [], expected: 0n },
  { name: "arrayAnyEmptySkipsPredicateTrap", args: [], expected: 0n },
  { name: "arrayAllScalars", args: [], expected: 1n },
  { name: "arrayAllWindowTrue", args: [], expected: 1n },
  { name: "arrayAllStructure", args: [], expected: 1n },
  { name: "arrayAnyStatus", args: [], expected: 1n },
  { name: "arrayAllEmptySkipsPredicateTrap", args: [], expected: 1n },
  { name: "arrayFilterScalarsRead", args: [], expected: 577n },
  { name: "arrayFilterWindowRead", args: [], expected: 25n },
  { name: "arrayFilterNoneSize", args: [], expected: 0n },
  { name: "arrayFilterStructureRead", args: [], expected: 3456n },
  { name: "arrayFilterStatusRead", args: [], expected: 72n },
  { name: "arrayFilterEmptySkipsPredicateTrap", args: [], expected: 0n },
  { name: "arrayUInt8Read", args: [], expected: 1044n },
  { name: "arrayUInt8SetRead", args: [], expected: 44n },
  { name: "arrayUInt8GetQuestion", args: [], expected: 5n },
  { name: "arrayUInt32MapRead", args: [], expected: 3n },
  { name: "arrayBoolRead", args: [], expected: 1n },
  { name: "arrayNatRead", args: [], expected: 103n },
  { name: "arrayStructureLiteralRead", args: [], expected: 1234n },
  { name: "arrayStructureSetRead", args: [], expected: 98n },
  { name: "arrayStructurePushRead", args: [], expected: 34n },
  { name: "arrayStructurePushHelperRead", args: [], expected: 89n },
  { name: "arrayStructurePopRead", args: [], expected: 12n },
  { name: "arrayStructureAppendRead", args: [], expected: 1234n },
  { name: "arrayStructureExtractRead", args: [], expected: 3456n },
  { name: "arrayStructureInsertRead", args: [], expected: 123456n },
  { name: "arrayStructureInsertSkipsValueTrap", args: [], expected: 12n },
  { name: "arrayStructureInsertSkipsHelperValueTrap", args: [], expected: 12n },
  { name: "arrayStructureEraseRead", args: [], expected: 1256n },
  { name: "arrayStructureSwapRead", args: [], expected: 563412n },
  { name: "arrayStructureReverseRead", args: [], expected: 563412n },
  { name: "arrayStructureGetDRead", args: [], expected: 78n },
  { name: "arrayStructureGetDSkipsDefaultTrap", args: [], expected: 12n },
  { name: "arrayStructureModifyRead", args: [], expected: 45n },
  { name: "arrayStructureModifyOutOfBoundsSkipsFunctionTrap", args: [], expected: 12n },
  { name: "arrayStructureSetIfInBoundsSkipsHelperValueTrap", args: [], expected: 12n },
  { name: "arrayStructureReplicateRead", args: [], expected: 1212n },
  { name: "arrayStructureReplicateHelperRead", args: [], expected: 8989n },
  { name: "arrayStructureMapRead", args: [], expected: 3375n },
  { name: "arrayStructureMapEmptySkipsFunctionTrap", args: [], expected: 0n },
  { name: "arrayStructureMapEmptySkipsHelperTrap", args: [], expected: 0n },
  { name: "arrayStructureFoldRead", args: [], expected: 1234n },
  { name: "arrayStructureSafeGet", args: [], expected: 45n },
  { name: "arrayStructureSafeNoneSkipsPayloadTrap", args: [], expected: 7n },
  { name: "arrayStatusLiteralMatch", args: [], expected: 57n },
  { name: "arrayStatusSwapMatch", args: [], expected: 1175n },
  { name: "arrayStatusReverseMatch", args: [], expected: 1175n },
  { name: "arrayStatusModifyMatch", args: [], expected: 107n },
  { name: "arrayStatusReplicateMatch", args: [], expected: 1077n },
  { name: "arrayStatusMapMatch", args: [], expected: 1168n },
  { name: "arrayOptionLiteralMatch", args: [], expected: 57n },
  { name: "arrayLiteralRead", args: [], expected: 1030n },
  { name: "arrayGetProof", args: [], expected: 10n },
  { name: "arrayEmptyLiteral", args: [], expected: 1n },
  { name: "arrayEmptyConstructors", args: [], expected: 1n },
  { name: "arrayEmptyCapacitySkipsTrap", args: [], expected: 1n },
  { name: "arraySingletonRead", args: [], expected: 42n },
  { name: "arrayIsEmptyValues", args: [], expected: 1n },
  { name: "arrayBackRead", args: [], expected: 9n },
  { name: "arrayProofBackRead", args: [], expected: 9n },
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
  { name: "nestedArrayLiteralRead", args: [], expected: 255n },
  { name: "nestedArraySetPushRead", args: [], expected: 933n },
  { name: "nestedArrayFoldSizes", args: [], expected: 5n },
  { name: "nestedArrayMapPushRead", args: [], expected: 299n },
  { name: "nestedArrayFindRead", args: [], expected: 5n },
  {
    name: "publicNestedArrayReturn",
    args: [],
    expected: null,
    memoryValues: [{ resultIndex: 0, layout: nestedU64ArrayLayout, value: [[1n, 2n]] }],
  },
  {
    name: "publicNestedArrayParam",
    args: [{ layout: nestedU64ArrayLayout, value: [[1n, 2n], [3n, 4n, 5n]] }],
    expected: 15n,
  },
  {
    name: "publicNestedArrayOpsReturn",
    args: [{ layout: nestedU64ArrayLayout, value: [[1n, 2n], [3n, 4n, 5n]] }],
    expected: null,
    memoryValues: [{ resultIndex: 0, layout: nestedU64ArrayLayout, value: [[99n, 100n], [3n, 4n, 5n, 3n], [1n, 2n, 2n]] }],
  },
  {
    name: "publicByteArrayArrayReturn",
    args: [],
    expected: null,
    memoryValues: [{ resultIndex: 0, layout: byteArrayArrayLayout, value: [[65], [66, 67]] }],
  },
  {
    name: "publicByteArrayArrayParam",
    args: [{ layout: byteArrayArrayLayout, value: [[65], [66, 67], [68, 69, 70]] }],
    expected: 6n,
  },
  {
    name: "publicOptionArrayReturn",
    args: [],
    expected: [1n, null],
    memoryValues: [{ resultIndex: 1, layout: byteArrayArrayLayout, value: [[65], [66, 67]] }],
  },
  {
    name: "publicOptionArrayParam",
    args: [{ layout: optionArrayByteArrayLayout, value: { tag: 1, fields: [[[65], [66, 67]]] } }],
    expected: 3n,
  },
  {
    name: "publicExceptArrayReturn",
    args: [],
    expected: [1n, 0n, 0n, null],
    memoryValues: [{ resultIndex: 3, layout: byteArrayArrayLayout, value: [[65], [66, 67]] }],
  },
  {
    name: "publicExceptArrayParam",
    args: [{ layout: exceptByteArrayArrayLayout, value: { tag: 1, fields: [[[65], [66, 67]]] } }],
    expected: 13n,
  },
  {
    name: "publicOptionByteArrayArrayReturn",
    args: [],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: optionByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[65]] },
          { tag: 0, fields: [] },
          { tag: 1, fields: [[66, 67]] },
        ],
      },
    ],
  },
  {
    name: "publicOptionByteArrayArrayParam",
    args: [
      {
        layout: optionByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[65]] },
          { tag: 0, fields: [] },
          { tag: 1, fields: [[66, 67]] },
        ],
      },
    ],
    expected: 13n,
  },
  {
    name: "publicOptionByteArrayArrayOpsReturn",
    args: [
      {
        layout: optionByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[65]] },
          { tag: 0, fields: [] },
          { tag: 1, fields: [[66, 67]] },
        ],
      },
    ],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: optionByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[66, 67, 33]] },
          { tag: 0, fields: [] },
          { tag: 1, fields: [[65, 33]] },
        ],
      },
    ],
  },
  {
    name: "publicOptionByteArrayArrayFullOps",
    args: [{ layout: optionByteArrayArrayLayout, value: optionByteArrayArraySample }],
    expected: [1n, 0n, 1033310n],
  },
  {
    name: "publicOptionByteArrayArrayFullOpsReturn",
    args: [{ layout: optionByteArrayArrayLayout, value: optionByteArrayArraySample }],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: optionByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[71, 72, 73, 33]] },
          { tag: 1, fields: [[74, 75, 33]] },
          { tag: 1, fields: [[66, 67, 33]] },
        ],
      },
    ],
  },
  {
    name: "publicExceptByteArrayArrayReturn",
    args: [],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: exceptByteArrayByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[65]] },
          { tag: 0, fields: [[66, 67]] },
          { tag: 1, fields: [[68, 69, 70]] },
        ],
      },
    ],
  },
  {
    name: "publicExceptByteArrayArrayParam",
    args: [
      {
        layout: exceptByteArrayByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[65]] },
          { tag: 0, fields: [[66, 67]] },
          { tag: 1, fields: [[68, 69, 70]] },
        ],
      },
    ],
    expected: 24n,
  },
  {
    name: "publicExceptByteArrayArrayFullOps",
    args: [{ layout: exceptByteArrayByteArrayArrayLayout, value: exceptByteArrayByteArrayArraySample }],
    expected: [1n, 0n, 7660011n],
  },
  {
    name: "publicExceptByteArrayArrayFullOpsReturn",
    args: [{ layout: exceptByteArrayByteArrayArrayLayout, value: exceptByteArrayByteArrayArraySample }],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: exceptByteArrayByteArrayArrayLayout,
        value: [
          { tag: 1, fields: [[72, 73, 33]] },
          { tag: 1, fields: [[74, 75, 33]] },
          { tag: 0, fields: [[76, 77, 78, 63]] },
        ],
      },
    ],
  },
  {
    name: "publicTokenArrayReturn",
    args: [],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: tokenArrayLayout,
        value: [
          { tag: 0, fields: [[65]] },
          { tag: 1, fields: [7n] },
          { tag: 0, fields: [[66, 67]] },
        ],
      },
    ],
  },
  {
    name: "publicTokenArrayParam",
    args: [
      {
        layout: tokenArrayLayout,
        value: [
          { tag: 0, fields: [[65]] },
          { tag: 1, fields: [7n] },
          { tag: 0, fields: [[66, 67]] },
        ],
      },
    ],
    expected: 10n,
  },
  {
    name: "publicTokenArrayOpsReturn",
    args: [
      {
        layout: tokenArrayLayout,
        value: [
          { tag: 0, fields: [[65]] },
          { tag: 1, fields: [7n] },
          { tag: 0, fields: [[66, 67]] },
        ],
      },
    ],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: tokenArrayLayout,
        value: [
          { tag: 0, fields: [[66, 67, 33]] },
          { tag: 1, fields: [8n] },
          { tag: 0, fields: [[65, 33]] },
        ],
      },
    ],
  },
  {
    name: "publicTokenArrayFullOps",
    args: [{ layout: tokenArrayLayout, value: publicTokenArraySample }],
    expected: [1n, 0n, 2324011n],
  },
  {
    name: "publicTokenArrayFullOpsReturn",
    args: [{ layout: tokenArrayLayout, value: publicTokenArraySample }],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: tokenArrayLayout,
        value: [
          { tag: 0, fields: [[71, 72, 73, 33]] },
          { tag: 1, fields: [12n] },
        ],
      },
    ],
  },
  {
    name: "publicByteArrayGroupReturn",
    args: [],
    expected: [null, 9n],
    memoryValues: [{ resultIndex: 0, layout: byteArrayArrayLayout, value: [[65], [66, 67]] }],
  },
  {
    name: "publicByteArrayGroupParam",
    args: [{ layout: byteArrayGroupLayout, value: { values: [[65], [66, 67]], marker: 9n } }],
    expected: 12n,
  },
  {
    name: "publicByteArrayGroupArrayReturn",
    args: [],
    expected: null,
    memoryValues: [{ resultIndex: 0, layout: byteArrayGroupArrayLayout, value: byteArrayGroupArraySample }],
  },
  {
    name: "publicByteArrayGroupArrayParam",
    args: [{ layout: byteArrayGroupArrayLayout, value: byteArrayGroupArraySample }],
    expected: 504n,
  },
  {
    name: "publicByteArrayGroupArrayFullOps",
    args: [{ layout: byteArrayGroupArrayLayout, value: byteArrayGroupArraySample }],
    expected: [1n, 0n, 241502704111n],
  },
  {
    name: "publicByteArrayGroupArrayFullOpsReturn",
    args: [{ layout: byteArrayGroupArrayLayout, value: byteArrayGroupArraySample }],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: byteArrayGroupArrayLayout,
        value: [
          { values: [[76, 77, 78], [90]], marker: 8n },
          { values: [[73, 74], [75], [90]], marker: 7n },
        ],
      },
    ],
  },
  {
    name: "publicNestedTaggedArrayReturn",
    args: [],
    expected: [1n, null],
    memoryValues: [{ resultIndex: 1, layout: optionByteArrayArrayLayout, value: optionByteArrayArraySample }],
  },
  {
    name: "publicNestedTaggedArrayParam",
    args: [{ layout: optionArrayOptionByteArrayLayout, value: { tag: 1, fields: [optionByteArrayArraySample] } }],
    expected: 13n,
  },
  { name: "optionByteArrayArrayEquality", args: [], expected: 1n },
  { name: "publicTokenArrayEquality", args: [], expected: 1n },
  { name: "byteArrayGroupArrayEquality", args: [], expected: 1n },
  {
    name: "publicHeapArrayResultReturn",
    args: [0n],
    expected: [0n, null, 3n, 0n, 0n],
    memoryBytes: [{ resultIndex: 1, lengthIndex: 2, values: [98, 97, 100] }],
  },
  {
    name: "publicHeapArrayResultReturn",
    args: [1n],
    expected: [1n, 0n, 0n, null, 5n],
    memoryValues: [{ resultIndex: 3, layout: byteArrayArrayLayout, value: [[65], [66, 67]] }],
  },
  {
    name: "publicHeapArrayResultParam",
    args: [
      {
        layout: heapArrayResultLayout,
        value: { tag: 1, fields: [[[65], [66, 67]], 5n] },
      },
    ],
    expected: 8n,
  },
  {
    name: "publicByteOutputStateArrayReturn",
    args: [],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: byteOutputStateArrayLayout,
        value: [{ count: 1n, bytes: [65] }, { count: 2n, bytes: [66, 67] }],
      },
    ],
  },
  {
    name: "publicByteOutputStateArrayParam",
    args: [
      {
        layout: byteOutputStateArrayLayout,
        value: [{ count: 1n, bytes: [65] }, { count: 2n, bytes: [66, 67] }],
      },
    ],
    expected: 6n,
  },
  {
    name: "publicArrayBoxArrayReturn",
    args: [],
    expected: null,
    memoryValues: [{ resultIndex: 0, layout: arrayBoxArrayLayout, value: [{ values: [1n, 2n], count: 2n }] }],
  },
  {
    name: "publicArrayBoxArrayParam",
    args: [
      {
        layout: arrayBoxArrayLayout,
        value: [{ values: [1n, 2n], count: 2n }, { values: [3n], count: 1n }],
      },
    ],
    expected: 9n,
  },
  {
    name: "publicByteArrayArrayOps",
    args: [{ layout: byteArrayArrayLayout, value: [[65], [66, 67], [68, 69, 70]] }],
    expected: [1n, 0n, 1234211n],
  },
  {
    name: "publicByteArrayArrayOpsReturn",
    args: [{ layout: byteArrayArrayLayout, value: [[65], [66, 67], [68, 69, 70]] }],
    expected: null,
    memoryValues: [
      {
        resultIndex: 0,
        layout: byteArrayArrayLayout,
        value: [[68, 69, 70, 33], [66, 67, 33], [90, 90, 33]],
      },
    ],
  },
  { name: "arrayBoxElementRead", args: [], expected: 223n },
  { name: "arrayProductElementRead", args: [], expected: 43n },
  { name: "recLetDemo", args: [], expected: 518n },
  { name: "recExitDemo", args: [], expected: 314n },
  { name: "recThenBranchExitDemo", args: [], expected: 13n },
  { name: "recThenBranchFuelDemo", args: [], expected: 2n },
  { name: "recProductDemo", args: [], expected: 10n },
  { name: "recStepLetDemo", args: [], expected: 5n },
  { name: "recStepLetExitDemo", args: [], expected: 13n },
  { name: "recStepUnusedLetSkipsTrap", args: [], expected: 3n },
  { name: "recPointFuel", args: [2n, 5n], expected: [7n, 8n] },
  { name: "recPointFuelCallRead", args: [2n, 5n], expected: 78n },
  { name: "recStatusExitFuel", args: [10n, 1n], expected: [1n, 0n, 3n] },
  { name: "recStatusExitFuel", args: [1n, 1n], expected: [0n, 2n, 0n] },
  { name: "recPointCarryFuel", args: [3n, 1n, 10n], expected: [4n, 16n] },
  { name: "recStatusCarryFuel", args: [2n, 0n, 5n, 0n], expected: 7n },
  { name: "recStatusCarryFuel", args: [2n, 1n, 0n, 5n], expected: 107n },
  { name: "recursiveDemandedFuelGet", args: [], expected: 7n },
  { name: "u64ListHeadDemo", args: [], expected: 1n },
  { name: "u64ListTailHeadDemo", args: [], expected: 2n },
  { name: "u64ListNilDemo", args: [], expected: 7n },
  { name: "u64ListSumDemo", args: [], expected: 6n },
  { name: "u64ListSumShortFuel", args: [], expected: 3n },
  { name: "u64ListStructuralSumDemo", args: [], expected: 6n },
  { name: "u64ListBranch", args: [0n], expected: 0n },
  { name: "u64ListBranch", args: [1n], expected: 9n },
  { name: "u64ListArrayLiteralHeadSum", args: [], expected: 10n },
  { name: "u64ListArrayPushSetSum", args: [], expected: 6n },
  { name: "u64ListArrayMapTailHead", args: [], expected: 2n },
  { name: "u64ListArrayFoldHeads", args: [], expected: 10n },
  { name: "u64ListArrayRuntimeReleaseFrees", args: [], expected: 103n },
  { name: "leanListHeadDemo", args: [], expected: 1n },
  { name: "leanListTailHeadDemo", args: [], expected: 2n },
  { name: "leanListStructuralSumDemo", args: [], expected: 6n },
  { name: "leanListMapDemo", args: [], expected: 2n },
  { name: "leanListMapDirectDemo", args: [], expected: 2n },
  { name: "leanListMapDirectBranchDemo", args: [0n], expected: 10n },
  { name: "leanListMapDirectBranchDemo", args: [1n], expected: 2n },
  { name: "leanListFilterDemo", args: [], expected: 2n },
  { name: "leanListFilterDirectDemo", args: [], expected: 2n },
  { name: "leanListLengthDirectDemo", args: [], expected: 3n },
  { name: "leanListLengthRecDemo", args: [], expected: 3n },
  { name: "leanListAppendDirectDemo", args: [], expected: 15n },
  { name: "leanListAppendDirectBranchDemo", args: [0n], expected: 6n },
  { name: "leanListAppendDirectBranchDemo", args: [1n], expected: 15n },
  { name: "leanListAppendRecDemo", args: [], expected: 15n },
  { name: "leanListConcatDirectDemo", args: [4n], expected: 10n },
  { name: "leanListReverseDirectDemo", args: [], expected: 3n },
  { name: "leanListReverseRecDemo", args: [], expected: 3n },
  { name: "leanListFoldrDemo", args: [], expected: 321n },
  { name: "leanListFoldrRecDemo", args: [], expected: 321n },
  { name: "leanListFindDemo", args: [], expected: 2n },
  { name: "leanListFindMissingDemo", args: [], expected: 0n },
  { name: "leanListFoldlDemo", args: [], expected: 123n },
  { name: "leanListFoldlClosedDemo", args: [], expected: 123n },
  { name: "leanListFoldlClosedStructDemo", args: [], expected: 36n },
  { name: "leanListAnyDemo", args: [], expected: 1n },
  { name: "leanListAnyMissingDemo", args: [], expected: 0n },
  { name: "leanListAnyDirectDemo", args: [], expected: 1n },
  { name: "leanListAnyDirectMissingDemo", args: [], expected: 0n },
  { name: "leanListAllDirectDemo", args: [], expected: 1n },
  { name: "leanListAllDirectMissingDemo", args: [], expected: 0n },
  { name: "leanListBoxScoreDemo", args: [], expected: 86n },
  { name: "leanListScenarioScore", args: [0n, 7n], expected: 0n },
  { name: "leanListScenarioScore", args: [1n, 7n], expected: 1077n },
  { name: "leanListScenarioScore", args: [2n, 2n], expected: 3062n },
  { name: "leanListScenarioScore", args: [3n, 99n], expected: 4760n },
  { name: "u64TreeArrayFieldDemo", args: [], expected: 7n },
  { name: "u64TreeSizeDemo", args: [], expected: 6n },
  { name: "u64BinaryStructuralSizeDemo", args: [], expected: 3n },
  { name: "u64BinaryScenarioScore", args: [0n, 5n], expected: 10151n },
  { name: "u64BinaryScenarioScore", args: [0n, 9n], expected: 10150n },
  { name: "u64BinaryScenarioScore", args: [1n, 4n], expected: 70401n },
  { name: "u64BinaryScenarioScore", args: [2n, 9n], expected: 70500n },
  { name: "u64BinaryShapeDemo", args: [], expected: 531n },
  { name: "u64BinaryMapLeafSumDemo", args: [], expected: 9n },
  { name: "u64BinaryMirrorLeftmostDemo", args: [], expected: 3n },
  { name: "u64BinaryInsertShapeDemo", args: [], expected: 745n },
  { name: "u64BinaryFindOptionDemo", args: [], expected: 2n },
  { name: "u64BinaryFindMissingDemo", args: [], expected: 7n },
  { name: "u64BinaryRequireOkDemo", args: [], expected: 12n },
  { name: "u64BinaryRequireErrorDemo", args: [], expected: 9n },
  { name: "u64BinaryBoxScoreDemo", args: [], expected: 706n },
  { name: "u64BinarySharedChildScore", args: [], expected: 70306n },
  { name: "u64BinaryReturnedSubtreeAliasScore", args: [], expected: 317n },
  { name: "u64BinarySharedArrayScore", args: [], expected: 714n },
  { name: "u64BinarySharedStructAliasScore", args: [], expected: 30329n },
  { name: "u64BinarySharedTaggedAliasScore", args: [], expected: 30342n },
  { name: "u64ExprEvalDemo", args: [], expected: 45n },
  { name: "recursiveStructFieldDemo", args: [], expected: 21n },
  { name: "recursiveStructArrayFoldDemo", args: [], expected: 24n },
  { name: "recursiveTaggedPayloadDemo", args: [], expected: 17n },
  { name: "recursiveTaggedArrayFindDemo", args: [], expected: 19n },
  { name: "mutualJsonArrayDemo", args: [], expected: 4n },
  { name: "mutualJsonObjectDemo", args: [], expected: 60n },
  { name: "mutualWrappedFieldArrayDemo", args: [], expected: 55n },
  { name: "mutualTaggedArrayFindDemo", args: [], expected: 102n },
  { name: "mutualStructuralJsonSizeDemo", args: [], expected: 10n },
  { name: "mutualStructuralFieldSizeDemo", args: [], expected: 11n },
  { name: "mutualStructuralTriADemo", args: [], expected: 21n },
  { name: "mutualStructuralTriBDemo", args: [], expected: 15n },
  { name: "mutualStructuralTriCDemo", args: [], expected: 15n },
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
  { name: "exceptUnitErrorOk", args: [], expected: 1n },
  { name: "exceptUnitErrorError", args: [], expected: 7n },
  { name: "exceptUnitErrorBind", args: [], expected: 5n },
  { name: "optionDoSome", args: [], expected: 7n },
  { name: "optionDoNoneSkipsRestTrap", args: [], expected: 7n },
  { name: "optionFunctorMapSome", args: [], expected: 6n },
  { name: "optionFunctorMapNoneSkipsFunctionTrap", args: [], expected: 7n },
  { name: "exceptDoOk", args: [], expected: 7n },
  { name: "exceptDoErrorSkipsRestTrap", args: [], expected: 7n },
  { name: "exceptFunctorMapOk", args: [], expected: 6n },
  { name: "exceptFunctorMapErrorSkipsFunctionTrap", args: [], expected: 7n },
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
    name: "rejectUnitReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUnitReturn",
  },
  {
    name: "rejectUnitParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectUnitParam",
  },
  {
    name: "rejectRuntimeStringToUTF8",
    message: "unsupported String.toUTF8 argument: expected compile-time string expression",
  },
  {
    name: "rejectRuntimeStringLength",
    message: "unsupported String.length argument: expected compile-time string expression",
  },
  {
    name: "rejectStringParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectStringParam",
  },
  {
    name: "rejectRecursiveInductiveEquality",
    message: "unsupported equality type: LeanExe.IR.Ty.recVariant `LeanExe.Examples.Correctness.EqU64List []",
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
    name: "rejectRecursiveInductiveParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveInductiveParam",
  },
  {
    name: "rejectRecursiveInductiveReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveInductiveReturn",
  },
  {
    name: "rejectRecursiveArrayParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveArrayParam",
  },
  {
    name: "rejectRecursiveArrayReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveArrayReturn",
  },
  {
    name: "rejectRecursiveStructParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveStructParam",
  },
  {
    name: "rejectRecursiveTaggedParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveTaggedParam",
  },
  {
    name: "rejectRecursiveOptionArrayParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveOptionArrayParam",
  },
  {
    name: "rejectRecursiveOptionArrayReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveOptionArrayReturn",
  },
  {
    name: "rejectRecursiveStructArrayParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveStructArrayParam",
  },
  {
    name: "rejectRecursiveTaggedArrayParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectRecursiveTaggedArrayParam",
  },
  {
    name: "rejectMutualJsonParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectMutualJsonParam",
  },
  {
    name: "rejectMutualFieldParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectMutualFieldParam",
  },
  {
    name: "rejectMutualJsonReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectMutualJsonReturn",
  },
  {
    name: "rejectMutualFieldArrayReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectMutualFieldArrayReturn",
  },
  {
    name: "rejectListFoldlLocalCallback",
    message: "unsupported expression-level structural recursion: List",
  },
  {
    name: "rejectListFoldlFunctionAccumulator",
    message: "unsupported let-bound type: UInt64 -> UInt64",
  },
  {
    name: "rejectListNestedClosedFold",
    message: "unsupported structural recursion carried arguments",
  },
  {
    name: "rejectListFoldlTaggedAccumulator",
    message:
      "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectListFoldlTaggedAccumulator.match_1",
  },
  {
    name: "rejectHigherOrder",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectHigherOrder",
  },
  {
    name: "rejectIdRunFunctionValue",
    message: "unsupported let-bound type",
  },
  {
    name: "rejectIO",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectIO",
  },
];

const trapped = [
  { name: "natAddOverflow", args: [] },
  { name: "natMulOverflow", args: [] },
  { name: "natSuccOverflow", args: [] },
  { name: "optionGetBangNoneTrap", args: [] },
  { name: "arrayBackEmptyTrap", args: [] },
  { name: "arrayInsertIdxBangTrap", args: [] },
  { name: "arrayEraseIdxBangTrap", args: [] },
  { name: "byteArrayPushSizeForcesValueTrap", args: [] },
  { name: "byteArrayAppendSizeForcesRightTrap", args: [] },
  { name: "byteArraySetSizeForcesValueTrap", args: [] },
  { name: "byteArraySetBangTrap", args: [] },
  { name: "byteArrayToUInt64Trap", args: [] },
  { name: "byteArrayMkSizeForcesArrayTrap", args: [] },
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

function compileWat(name, out) {
  return run([
    leanExe,
    "compile-wat",
    "--module",
    moduleName,
    "--entry",
    `${moduleName}.${name}`,
    "--out",
    out,
  ]);
}

function checkWatSize(testCase) {
  const out = path.join(outDir, `${testCase.name}.wat`);
  const compiled = compileWat(testCase.name, out);
  if (compiled.status !== 0) {
    throw new Error(`${testCase.name} failed to compile WAT: ${compiled.stderr.trim()}`);
  }
  const size = fs.statSync(out).size;
  if (size > testCase.maxBytes) {
    throw new Error(`${testCase.name}: WAT is ${size} bytes, expected at most ${testCase.maxBytes}`);
  }
}

async function runAccepted(testCase) {
  const out = path.join(outDir, `${testCase.name}.wasm`);
  const compiled = compile(testCase.name, out);
  if (compiled.status !== 0) {
    throw new Error(`${testCase.name} failed to compile: ${compiled.stderr.trim()}`);
  }

  const resultCount = Array.isArray(testCase.expected) ? testCase.expected.length : 1;
  const needsMemory =
    (testCase.memoryArrays || []).length > 0 ||
    (testCase.memoryBytes || []).length > 0 ||
    (testCase.memoryValues || []).length > 0;
  const needsPlan = needsMemory || testCase.args.some((arg) => arg && typeof arg === "object" && arg.layout);
  let actualSlots;
  let memory = null;

  if (needsPlan) {
    const plan = new HostPlan();
    testCase.args.forEach((arg) => materializeArgPlan(plan, arg));
    const result = host.script(out, plan.commands, testCase.name, resultCount, memoryReadCommands(testCase));
    actualSlots = result.slots.map((slot) => BigInt.asUintN(64, slot));
    if (needsMemory) {
      memory = new SparseMemory(result.memoryChunks);
    }
  } else if (Array.isArray(testCase.expected)) {
    const output = host.call(
      out,
      testCase.name,
      `slots:${resultCount}`,
      testCase.args.map((arg) => host.i64(arg)),
    );
    actualSlots = output.split(/\s+/).filter((value) => value.length > 0).map((value) => BigInt.asUintN(64, BigInt(value)));
  } else {
    actualSlots = [host.callI64(out, testCase.name, testCase.args.map((arg) => host.i64(arg)))];
  }

  if (Array.isArray(testCase.expected)) {
    if (actualSlots.length !== testCase.expected.length) {
      throw new Error(`${testCase.name}: expected ${testCase.expected}, got ${actualSlots}`);
    }
    for (let index = 0; index < actualSlots.length; index += 1) {
      const expected = testCase.expected[index];
      if (expected !== null && actualSlots[index] !== expected) {
        throw new Error(`${testCase.name}: expected ${testCase.expected}, got ${actualSlots}`);
      }
    }
    if (needsMemory) {
      checkMemoryExpectations(testCase, memory, actualSlots);
    }
  } else {
    if (testCase.expected === null) {
      checkMemoryExpectations(testCase, memory, actualSlots);
    } else if (actualSlots[0] !== testCase.expected) {
      throw new Error(`${testCase.name}: expected ${testCase.expected}, got ${actualSlots[0]}`);
    }
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

  const result = spawnSync(
    wasmtime,
    ["run", "--invoke", testCase.name, out, ...testCase.args.map((arg) => arg.toString())],
    { encoding: "utf8" },
  );
  if (result.status === 0) {
    throw new Error(`${testCase.name}: expected WASM trap`);
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

  for (const testCase of watSizeGuards) {
    checkWatSize(testCase);
  }

  process.stdout.write(
    `checked ${accepted.length} accepted, ${rejected.length} rejected, and ${trapped.length} trapped cases\n`
  );
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
