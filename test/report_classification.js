#!/usr/bin/env node

const path = require("path");
const { spawnSync } = require("child_process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");

function runReport(moduleName, entryName) {
  const result = spawnSync(
    leanExe,
    ["report", "--module", moduleName, "--entry", entryName],
    { encoding: "utf8" },
  );
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `report failed for ${entryName}`);
  }
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
    entryName: "LeanExe.Examples.Correctness.arrayStatusLiteralMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayOptionLiteralMatch",
    shape: "entry shape: UInt64",
  },
  {
    moduleName: "LeanExe.Examples.Correctness",
    entryName: "LeanExe.Examples.Correctness.arrayInsertIdxBangRead",
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
