#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.EulerRusanovStep";
const entry = "sodQuarterStepCheckedBits";
const sourceEntry = `${moduleName}.${entry}`;
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "euler-rusanov-step");

const expected = [
  0x0000000000000000n,
  0x3fe9e00000000000n,
  0x3fbcccccccccccccn,
  0x4000100000000000n,
  0x3fd4400000000000n,
  0x3fbccccccccccccen,
  0x3fe7c00000000000n,
];

function run(args) {
  return runChecked(args, { encoding: "utf8" }).stdout;
}

function occurrences(text, fragment) {
  return text.split(fragment).length - 1;
}

function expectOccurrences(label, text, fragment, expectedCount) {
  const actual = occurrences(text, fragment);
  if (actual !== expectedCount) {
    throw new Error(
      `${label}: expected ${expectedCount} occurrences of ${fragment}, got ${actual}`,
    );
  }
}

function functionBody(wat, index) {
  const marker = `(func (;${index};)`;
  const start = wat.indexOf(marker);
  if (start < 0) throw new Error(`WAT function ${index} was not found`);
  const end = wat.indexOf("  (func (;", start + marker.length);
  return wat.slice(start, end < 0 ? wat.length : end);
}

function exportedFunctionIndex(wat, exportName) {
  const match = wat.match(new RegExp(`\\(export "${exportName}" \\(func (\\d+)\\)\\)`));
  if (!match) throw new Error(`${exportName}: WAT export was not found`);
  return Number(match[1]);
}

function formatWord(value) {
  return `0x${value.toString(16).padStart(16, "0")}`;
}

function main() {
  fs.mkdirSync(outDir, { recursive: true });
  const wasm = path.join(outDir, `${entry}.wasm`);
  const watPath = path.join(outDir, `${entry}.wat`);

  run([
    leanExe,
    "compile",
    "--module", moduleName,
    "--entry", sourceEntry,
    "--out", wasm,
  ]);
  const ir = run([
    leanExe,
    "dump-ir",
    "--module", moduleName,
    "--entry", sourceEntry,
  ]);
  run([
    leanExe,
    "compile-wat",
    "--module", moduleName,
    "--entry", sourceEntry,
    "--out", watPath,
  ]);

  const output = host.call(wasm, entry, "slots:7", []);
  const actual = output.split(/\s+/).filter(Boolean).map((value) =>
    BigInt.asUintN(64, BigInt(value)));
  if (actual.length !== expected.length ||
      actual.some((value, index) => value !== expected[index])) {
    throw new Error(
      `${entry}():\n` +
        `expected ${expected.map(formatWord).join(" ")}\n` +
        `actual   ${actual.map(formatWord).join(" ")}`,
    );
  }

  expectOccurrences("Euler step IR", ir, "f64MulBits", 23);
  expectOccurrences("Euler step IR", ir, "f64AddBits", 29);
  expectOccurrences("Euler step IR", ir, "bitXor", 5);
  expectOccurrences("Euler step IR", ir, "LeanExe.Float64.mulBits", 0);
  expectOccurrences("Euler step IR", ir, "LeanExe.Float64.addBits", 0);

  const wat = fs.readFileSync(watPath, "utf8");
  const exportedIndex = exportedFunctionIndex(wat, entry);
  if (exportedIndex !== 6) {
    throw new Error(`${entry}: expected exported function index 6, got ${exportedIndex}`);
  }
  const fluxBody = functionBody(wat, 0);
  const updateBody = functionBody(wat, 2);
  const stepBody = functionBody(wat, exportedIndex);

  expectOccurrences("Euler flux helper WAT", fluxBody, "f64.mul", 22);
  expectOccurrences("Euler flux helper WAT", fluxBody, "f64.add", 27);
  expectOccurrences("Euler flux helper WAT", fluxBody, "i64.xor", 3);
  expectOccurrences("Euler update helper WAT", updateBody, "f64.mul", 1);
  expectOccurrences("Euler update helper WAT", updateBody, "f64.add", 2);
  expectOccurrences("Euler update helper WAT", updateBody, "i64.xor", 2);
  expectOccurrences("Euler step WAT", stepBody, "call 0", 3);
  expectOccurrences("Euler step WAT", stepBody, "call 2", 6);
  expectOccurrences("Euler step WAT", stepBody, "call ", 9);

  process.stdout.write(
    "checked fixed Euler step Wasmtime words, IR operations, and WAT call shape\n",
  );
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
