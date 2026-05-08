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
    entryName: "LeanExe.Examples.Correctness.arrayModifyInBounds",
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
];

for (const testCase of cases) {
  const report = runReport(testCase.moduleName, testCase.entryName);
  if (!report.includes(testCase.shape)) {
    throw new Error(`${testCase.entryName}: missing ${testCase.shape}`);
  }
  if (!report.includes("compile status: implemented by the first generic scalar/array/bytearray compiler fragment")) {
    throw new Error(`${testCase.entryName}: report does not show implemented compile status`);
  }
  if (report.includes("status: rejected")) {
    throw new Error(`${testCase.entryName}: report contains a rejected frontier item`);
  }
}

process.stdout.write(`checked ${cases.length} report classification cases\n`);
