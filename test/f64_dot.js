#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.Float64Bits";
const entry = "dotCheckedBits";
const sourceEntry = `${moduleName}.${entry}`;
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "f64-dot");
const usePrebuilt = process.env.LEANEXE_F64_DOT_PREBUILT === "1";

function run(args) {
  return runChecked(args, { encoding: "utf8" }).stdout;
}

function occurrences(text, fragment) {
  return text.split(fragment).length - 1;
}

function expectOccurrences(label, text, fragment, expected) {
  const actual = occurrences(text, fragment);
  if (actual !== expected) {
    throw new Error(`${label}: expected ${expected} occurrences of ${fragment}, got ${actual}`);
  }
}

function expectResult(wasm, left, right, expected) {
  const output = host.call(
    wasm,
    entry,
    "slots:2",
    [host.arrayU64(left), host.arrayU64(right)],
  );
  const actual = output.split(/\s+/).filter(Boolean).map((value) =>
    BigInt.asUintN(64, BigInt(value)));
  if (actual.length !== 2 || actual.some((value, index) => value !== expected[index])) {
    throw new Error(`${entry}: expected slots ${expected}, got ${actual}`);
  }
}

function main() {
  fs.mkdirSync(outDir, { recursive: true });
  const wasm = path.join(outDir, `${entry}.wasm`);
  const watPath = path.join(outDir, `${entry}.wat`);
  const irPath = path.join(outDir, `${entry}.ir`);

  if (!usePrebuilt) {
    run([
      leanExe,
      "compile",
      "--module", moduleName,
      "--entry", sourceEntry,
      "--out", wasm,
    ]);
    fs.writeFileSync(irPath, run([
      leanExe,
      "dump-ir",
      "--module", moduleName,
      "--entry", sourceEntry,
    ]));
    run([
      leanExe,
      "compile-wat",
      "--module", moduleName,
      "--entry", sourceEntry,
      "--out", watPath,
    ]);
  }

  expectResult(wasm, [], [], [0n, 0n]);
  expectResult(
    wasm,
    [0x3fe0000000000000n],
    [0x3fe0000000000000n],
    [0n, 0x3fd0000000000000n],
  );
  expectResult(
    wasm,
    [0x3fe0000000000000n, 0xbfe0000000000000n, 0x3fd0000000000000n],
    [0x3fe0000000000000n, 0x3fe0000000000000n, 0x3fe0000000000000n],
    [0n, 0x3fc0000000000000n],
  );
  expectResult(wasm, [0x3fe0000000000000n], [], [1n, 0n]);
  expectResult(
    wasm,
    [0x3fe0000000000000n, 0x3ff0000000000000n],
    [0x3fe0000000000000n, 0x3fe0000000000000n],
    [0n, 0x3fe8000000000000n],
  );

  const ir = fs.readFileSync(irPath, "utf8");
  expectOccurrences("dot IR", ir, "f64MulBits", 2);
  expectOccurrences("dot IR", ir, "f64AddBits", 1);
  expectOccurrences("dot IR", ir, "LeanExe.Float64.mulBits", 0);
  expectOccurrences("dot IR", ir, "LeanExe.Float64.addBits", 0);

  const wat = fs.readFileSync(watPath, "utf8");
  expectOccurrences("dot WAT", wat, "f64.mul", 2);
  expectOccurrences("dot WAT", wat, "f64.add", 1);
  expectOccurrences("dot WAT", wat, "f64.reinterpret_i64", 6);
  expectOccurrences("dot WAT", wat, "i64.reinterpret_f64", 3);

  process.stdout.write("checked runtime-length f64 dot execution, IR, and WAT shape\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
