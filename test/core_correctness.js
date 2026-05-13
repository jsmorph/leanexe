#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const moduleName = "LeanExe.Examples.Correctness";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "core-correctness");

const watSizeGuards = [
  { name: "arrayStructureReplicateHelperRead", maxBytes: 500_000 },
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
  { name: "structureProjection", args: [], expected: 7n },
  { name: "structureUpdateProjection", args: [], expected: 19n },
  { name: "structureHelperResult", args: [], expected: 56n },
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
  { name: "idRunByteArrayForSum", args: [], expected: 6n },
  { name: "idRunArrayForSum", args: [], expected: 6n },
  { name: "idRunArrayForBreakSum", args: [], expected: 3n },
  { name: "idRunArrayForContinueNoElse", args: [], expected: 6n },
  { name: "idRunByteArrayForState", args: [], expected: [3n, 6n] },
  { name: "idRunByteArrayForBreakSum", args: [], expected: 3n },
  { name: "idRunByteArrayForContinueNoElse", args: [], expected: 6n },
  { name: "idRunArrayForStatus", args: [], expected: [1n, 0n, 2n] },
  { name: "idRunArrayForStatusScore", args: [], expected: 102n },
  { name: "idRunRangeForCount", args: [], expected: 3n },
  { name: "idRunRangeForStepSum", args: [], expected: 9n },
  { name: "idRunRangeForState", args: [], expected: [3n, 9n] },
  { name: "idRunRangeForBreakSum", args: [], expected: 6n },
  { name: "idRunRangeForBreakNoElse", args: [], expected: 3n },
  { name: "idRunRangeForContinueNoElse", args: [], expected: 12n },
  { name: "idRunRangeForBreakState", args: [], expected: [3n, 6n] },
  { name: "idRunRangeForContinueState", args: [], expected: [4n, 11n] },
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
  { name: "arrayFoldStructAccumulator", args: [], expected: 36n },
  { name: "arrayFoldProductAccumulator", args: [], expected: 39n },
  { name: "arrayFoldStatusAccumulator", args: [], expected: 6n },
  { name: "arrayFoldArrayAccumulator", args: [], expected: 1113n },
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
  { name: "u64TreeArrayFieldDemo", args: [], expected: 7n },
  { name: "u64TreeSizeDemo", args: [], expected: 6n },
  { name: "u64BinaryStructuralSizeDemo", args: [], expected: 3n },
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
    name: "rejectNestedArrayReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectNestedArrayReturn",
  },
  {
    name: "rejectNestedArrayParam",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectNestedArrayParam",
  },
  {
    name: "rejectArrayBoxArrayReturn",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectArrayBoxArrayReturn",
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
    name: "rejectHigherOrder",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectHigherOrder",
  },
  {
    name: "rejectIO",
    message: "unsupported function type or declaration: LeanExe.Examples.Correctness.rejectIO",
  },
  {
    name: "rejectIdForByteArrayAccumulator",
    message: "unsupported for-in accumulator type",
  },
  {
    name: "rejectIdRangeForByteArrayAccumulator",
    message: "unsupported for-in accumulator type",
  },
  {
    name: "rejectArrayFoldByteArrayAccumulator",
    message: "unsupported Array.foldl accumulator type",
  },
  {
    name: "rejectByteArrayFoldByteArrayAccumulator",
    message: "unsupported ByteArray.foldl accumulator type",
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
  if (Array.isArray(testCase.expected)) {
    if (!Array.isArray(result)) {
      throw new Error(`${testCase.name}: expected multi-value result, got ${result}`);
    }
    const actual = result.map((item) => BigInt.asUintN(64, item));
    if (actual.length !== testCase.expected.length) {
      throw new Error(`${testCase.name}: expected ${testCase.expected}, got ${actual}`);
    }
    for (let index = 0; index < actual.length; index += 1) {
      const expected = testCase.expected[index];
      if (expected !== null && actual[index] !== expected) {
        throw new Error(`${testCase.name}: expected ${testCase.expected}, got ${actual}`);
      }
    }
    for (const memoryArray of testCase.memoryArrays || []) {
      const ptr = actual[memoryArray.resultIndex];
      const view = new DataView(instance.exports.memory.buffer);
      const len = view.getBigUint64(Number(ptr), true);
      const expectedLength = memoryArray.length ?? memoryArray.values.length;
      if (len !== BigInt(expectedLength)) {
        throw new Error(`${testCase.name}: expected array length ${expectedLength}, got ${len}`);
      }
      for (let index = 0; index < memoryArray.values.length; index += 1) {
        const cell = view.getBigUint64(Number(ptr + BigInt(8 * (index + 1))), true);
        if (cell !== memoryArray.values[index]) {
          throw new Error(`${testCase.name}: expected array[${index}] ${memoryArray.values[index]}, got ${cell}`);
        }
      }
    }
    for (const memoryBytes of testCase.memoryBytes || []) {
      const ptr = actual[memoryBytes.resultIndex];
      const len = actual[memoryBytes.lengthIndex];
      const expectedLength = BigInt(memoryBytes.values.length);
      if (len !== expectedLength) {
        throw new Error(`${testCase.name}: expected byte length ${expectedLength}, got ${len}`);
      }
      const bytes = new Uint8Array(instance.exports.memory.buffer, Number(ptr), Number(len));
      for (let index = 0; index < memoryBytes.values.length; index += 1) {
        if (bytes[index] !== memoryBytes.values[index]) {
          throw new Error(`${testCase.name}: expected byte[${index}] ${memoryBytes.values[index]}, got ${bytes[index]}`);
        }
      }
    }
  } else {
    const actual = BigInt.asUintN(64, result);
    if (actual !== testCase.expected) {
      throw new Error(`${testCase.name}: expected ${testCase.expected}, got ${actual}`);
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
