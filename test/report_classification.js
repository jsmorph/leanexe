#!/usr/bin/env node

const path = require("path");
const { runChecked } = require("../tools/run-process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");

function runReport(moduleName, entryName) {
  const result = runChecked(
    [leanExe, "report", "--module", moduleName, "--entry", entryName],
    { encoding: "utf8" },
  );
  return result.stdout;
}

const cases = [
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.natMatchZero",
    shape: "entry shape: Nat -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.byteAtQuestionOrZero",
    shape: "entry shape: ByteArray -> Nat -> Nat",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.foldSum",
    shape: "entry shape: ByteArray -> Nat",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.findQuestion",
    shape: "entry shape: ByteArray -> Option Nat",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.readUInt64LE",
    shape: "entry shape: ByteArray -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.appendBang",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.mkABC",
    shape: "entry shape: ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.appendABCXYZ",
    shape: "entry shape: ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.appendInputABC",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.appendNotationABCXYZ",
    shape: "entry shape: ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.setABC",
    shape: "entry shape: ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.setFirstBang",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.setBangFirstQuestion",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.copyInputMiddle",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.ByteArrayPrograms",
    entryName: "LeanExe.Examples.ByteArrayPrograms.tailSlice",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.AsciiStringPrograms",
    entryName: "LeanExe.Examples.AsciiStringPrograms.validAscii",
    shape: "entry shape: ByteArray -> Bool",
  },
  {
    moduleName: "LeanExe.Examples.AsciiStringPrograms",
    entryName: "LeanExe.Examples.AsciiStringPrograms.identityTrusted",
    shape: "entry shape: LeanExe.AsciiString -> LeanExe.AsciiString",
  },
  {
    moduleName: "LeanExe.Examples.AsciiStringPrograms",
    entryName: "LeanExe.Examples.AsciiStringPrograms.appendBangOrQuestion",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.AsciiStringPrograms",
    entryName: "LeanExe.Examples.AsciiStringPrograms.pushIfAscii",
    shape: "entry shape: ByteArray -> UInt64 -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.AsciiStringPrograms",
    entryName: "LeanExe.Examples.AsciiStringPrograms.appendSelfTrusted",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.optionBindProduct",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.productHelperResult",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.structureReturn",
    shape: "entry shape: UInt64 -> LeanExe.Examples.Correctness.Point",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.structurePointArrayReturn",
    shape: "entry shape: LeanExe.Examples.Correctness.PointArrayBox",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.structureParam",
    shape: "entry shape: LeanExe.Examples.Correctness.Point -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.proofStructureReturn",
    shape: "entry shape: LeanExe.Examples.Correctness.CheckedPoint",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.proofStructureParam",
    shape: "entry shape: LeanExe.Examples.Correctness.CheckedPoint -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.statusBranchReturn",
    shape: "entry shape: UInt64 -> LeanExe.Examples.Correctness.Status",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.statusParam",
    shape: "entry shape: LeanExe.Examples.Correctness.Status -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.checkedStatusReturn",
    shape: "entry shape: LeanExe.Examples.Correctness.CheckedStatus",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.optionReturn",
    shape: "entry shape: UInt64 -> Option UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.optionParam",
    shape: "entry shape: Option UInt64 -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.exceptReturn",
    shape: "entry shape: UInt64 -> Except UInt64 UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.exceptParam",
    shape: "entry shape: Except UInt64 UInt64 -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.exceptBindProduct",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.optionDoSome",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.exceptDoOk",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.idRunBind",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.idFunctionUInt64",
    shape: "entry shape: UInt64 -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.exceptIsOkAsBool",
    shape: "entry shape: Bool",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.exceptMapErrorProduct",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.optionGetBangProduct",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.optionAnySome",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.boolToNatValue",
    shape: "entry shape: Bool -> Nat",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.natBoolComparisons",
    shape: "entry shape: Nat -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.natBeqAsBool",
    shape: "entry shape: Nat -> Bool",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayAppendNotationRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayBackQuestionRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayProofBackRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayModifyInBounds",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arraySetIfInBoundsRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayInsertIdxIfInBoundsMiddle",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayEraseIdxIfInBoundsMiddle",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arraySwapIfInBoundsEnds",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayReverseRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayProofInsertIdxRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arraySwapAtRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayMapRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayFoldSum",
    shape: "entry shape: Nat",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayFindIdxStructure",
    shape: "entry shape: Option Nat",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayFindStructure",
    shape: "entry shape: Option LeanExe.Examples.Correctness.Point",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayAllStructure",
    shape: "entry shape: Bool",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayFilterStructureRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicByteArrayArrayParam",
    shape: "entry shape: Array ByteArray -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicOptionArrayReturn",
    shape: "entry shape: Option Array ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicExceptArrayReturn",
    shape: "entry shape: Except ByteArray Array ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicOptionByteArrayArrayParam",
    shape: "entry shape: Array Option ByteArray -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicOptionByteArrayArrayFullOps",
    shape: "entry shape: Array Option ByteArray -> Except UInt64 UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicExceptByteArrayArrayFullOps",
    shape: "entry shape: Array Except ByteArray ByteArray -> Except UInt64 UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicTokenArrayParam",
    shape: "entry shape: Array LeanExe.Examples.Correctness.PublicToken -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicTokenArrayFullOps",
    shape: "entry shape: Array LeanExe.Examples.Correctness.PublicToken -> Except UInt64 UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicNestedArrayReturn",
    shape: "entry shape: Array Array UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicArrayBoxArrayParam",
    shape: "entry shape: Array LeanExe.Examples.Correctness.ArrayBox -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicByteArrayGroupParam",
    shape: "entry shape: LeanExe.Examples.Correctness.ByteArrayGroup -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicByteArrayGroupArrayReturn",
    shape: "entry shape: Array LeanExe.Examples.Correctness.ByteArrayGroup",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicByteArrayGroupArrayFullOps",
    shape: "entry shape: Array LeanExe.Examples.Correctness.ByteArrayGroup -> Except UInt64 UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicNestedTaggedArrayReturn",
    shape: "entry shape: Option Array Option ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicNestedTaggedArrayParam",
    shape: "entry shape: Option Array Option ByteArray -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicHeapArrayResultReturn",
    shape: "entry shape: UInt64 -> LeanExe.Examples.Correctness.PublicHeapArrayResult",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicByteArrayArrayOps",
    shape: "entry shape: Array ByteArray -> Except UInt64 UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.publicByteArrayArrayOpsReturn",
    shape: "entry shape: Array ByteArray -> Array ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.recPointFuel",
    shape: "entry shape: Nat -> UInt64 -> LeanExe.Examples.Correctness.Point",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.recPointFuelCallRead",
    shape: "entry shape: Nat -> UInt64 -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.recStatusExitFuel",
    shape: "entry shape: Nat -> UInt64 -> LeanExe.Examples.Correctness.Status",
  },
  {
    moduleName: "LeanExe.Examples.JsonDouble",
    entryName: "LeanExe.Examples.JsonDouble.transform",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.JsonAdd",
    entryName: "LeanExe.Examples.JsonAdd.transform",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.JsonCollatzLength",
    entryName: "LeanExe.Examples.JsonCollatzLength.transform",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.JsonTools",
    entryName: "LeanExe.Examples.JsonTools.transform",
    shape: "entry shape: ByteArray -> ByteArray",
  },
  {
    moduleName: "LeanExe.Examples.JsonTools",
    entryName: "LeanExe.Examples.JsonTools.lookup",
    shape: "entry shape: ByteArray -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.recPointCarryFuel",
    shape: "entry shape: Nat -> LeanExe.Examples.Correctness.Point -> LeanExe.Examples.Correctness.Point",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.recStatusCarryFuel",
    shape: "entry shape: Nat -> LeanExe.Examples.Correctness.Status -> UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayUInt8Read",
    shape: "entry shape: Nat",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayUInt32MapRead",
    shape: "entry shape: Nat",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayBoolRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayNatRead",
    shape: "entry shape: Nat",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureLiteralRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureAppendRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureExtractRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureInsertRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureReverseRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureGetDRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureModifyRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureReplicateRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStructureMapRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStatusLiteralMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStatusReverseMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStatusModifyMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStatusReplicateMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayStatusMapMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayOptionLiteralMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.u64TreeArrayFieldDemo",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayInsertIdxBangRead",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.typeclassScoreArrayFindDemo",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.typeclassScoreListFindDemo",
    shape: "entry shape: UInt64",
  },
];

for (const testCase of cases) {
  const report = runReport(testCase.moduleName, testCase.entryName);
  if (!report.includes(testCase.shape)) {
    throw new Error(`${testCase.entryName}: missing ${testCase.shape}`);
  }
  if (!report.includes("compile status: implemented by the first generic scalar/array/bytearray/structure/inductive compiler fragment")) {
    throw new Error(`${testCase.entryName}: report does not show implemented compile status`);
  }
  if (report.includes("status: rejected")) {
    throw new Error(`${testCase.entryName}: report contains a rejected frontier item`);
  }
}

process.stdout.write(`checked ${cases.length} report classification cases\n`);
