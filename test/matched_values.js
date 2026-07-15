#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const moduleName = "LeanExe.Examples.Correctness";
const clobModule = "LeanExe.Examples.Clob";
const outDir = path.join(".lake", "build", "matched-values");

function run(args) {
  const result = runChecked(args, { encoding: "utf8" });
  return result.stdout;
}

function dumpIr(module, entry) {
  return run([
    leanExe,
    "dump-ir",
    "--module",
    module,
    "--entry",
    `${module}.${entry}`,
  ]);
}

function occurrences(text, pattern) {
  return text.match(pattern)?.length || 0;
}

function expectCount(name, text, pattern, expected) {
  const actual = occurrences(text, pattern);
  if (actual !== expected) {
    throw new Error(`${name}: expected ${expected} occurrences, got ${actual}`);
  }
}

function exportedFunctionBody(wat, exportName) {
  const exportMatch = wat.match(new RegExp(`\\(export "${exportName}" \\(func (\\d+)\\)\\)`));
  if (!exportMatch) {
    throw new Error(`${exportName}: WAT export was not found`);
  }
  const marker = `(func (;${exportMatch[1]};)`;
  const start = wat.indexOf(marker);
  if (start < 0) {
    throw new Error(`${exportName}: WAT function ${exportMatch[1]} was not found`);
  }
  const end = wat.indexOf("  (func (;", start + marker.length);
  return wat.slice(start, end < 0 ? wat.length : end);
}

function main() {
  fs.mkdirSync(outDir, { recursive: true });

  const scalar = dumpIr(moduleName, "matchedScalarScore");
  expectCount("matchedScalarScore helper call", scalar, /LeanExe\.IR\.Stmt\.call/g, 1);

  const lazy = dumpIr(moduleName, "matchedScalarSkipsUnusedBranchField");
  expectCount("matchedScalarSkipsUnusedBranchField trap", lazy, /LeanExe\.IR\.Expr\.trap/g, 0);

  for (const entry of ["matchedFindIdxPoint", "matchedFindIdxArray"]) {
    const ir = dumpIr(moduleName, entry);
    expectCount(entry, ir, /LeanExe\.IR\.Expr\.arrayFindIdxSlots/g, 1);
  }

  const cancelIr = dumpIr(clobModule, "cancel");
  expectCount("Clob.cancel IR scan", cancelIr, /LeanExe\.IR\.Expr\.arrayFindIdxSlots/g, 1);

  const watPath = path.join(outDir, "clob-cancel.wat");
  run([
    leanExe,
    "compile-wat",
    "--module",
    clobModule,
    "--entry",
    `${clobModule}.cancel`,
    "--out",
    watPath,
  ]);
  const cancelBody = exportedFunctionBody(fs.readFileSync(watPath, "utf8"), "cancel");
  expectCount(
    "Clob.cancel WAT predicate",
    cancelBody,
    /local\.get 2\s+local\.get 1\s+i64\.eq\s+if \(result i64\)/g,
    1,
  );

  process.stdout.write("checked 4 matched-value IR cases and 1 WAT scan case\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
