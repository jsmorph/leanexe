#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.EulerRusanov";
const entry = "rusanovFluxCheckedBits";
const sourceEntry = `${moduleName}.${entry}`;
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "euler-rusanov");

const bits = {
  zero: 0x0000000000000000n,
  negativeZero: 0x8000000000000000n,
  one: 0x3ff0000000000000n,
  half: 0x3fe0000000000000n,
  quarter: 0x3fd0000000000000n,
  eighth: 0x3fc0000000000000n,
  sixteenth: 0x3fb0000000000000n,
  tenth: 0x3fb999999999999an,
  negativeHalf: 0xbfe0000000000000n,
};

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

function formatWord(value) {
  return `0x${value.toString(16).padStart(16, "0")}`;
}

function expectResult(wasm, args, expected) {
  const output = host.call(wasm, entry, "slots:4", args.map(host.i64));
  const actual = output.split(/\s+/).filter(Boolean).map((value) =>
    BigInt.asUintN(64, BigInt(value)));
  if (actual.length !== expected.length || actual.some((value, index) => value !== expected[index])) {
    throw new Error(
      `${entry}(${args.map(formatWord).join(", ")}):\n` +
        `expected ${expected.map(formatWord).join(" ")}\n` +
        `actual   ${actual.map(formatWord).join(" ")}`,
    );
  }
}

function expectRejected(wasm, args) {
  expectResult(wasm, args, [1n, 0n, 0n, 0n]);
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

  const left = [bits.one, bits.zero, bits.one];
  const right = [bits.eighth, bits.zero, bits.tenth];
  const middle = [bits.half, bits.quarter, bits.quarter];
  const bottom = [bits.eighth, bits.negativeHalf, bits.sixteenth];
  const top = [bits.one, bits.half, bits.one];

  for (const [leftState, rightState, expected] of [
    [left, left, [0n, 0n, 0x3ff0000000000000n, 0n]],
    [right, right, [0n, 0n, 0x3fb999999999999an, 0n]],
    [left, right, [0n, 0x3fe8800000000000n, 0x3fe199999999999an, 0x3fff800000000000n]],
    [right, left, [0n, 0xbfe8800000000000n, 0x3fe199999999999an, 0xbfff800000000000n]],
    [middle, middle, [0n, 0x3fc0000000000000n, 0x3fd2000000000000n, 0x3fcc800000000000n]],
    [bottom, top, [0n, 0xbfe1800000000000n, 0x3fc7000000000000n, 0xbff4c80000000000n]],
    [top, bottom, [0n, 0x3fef800000000000n, 0x3ff2a00000000000n, 0x4007f40000000000n]],
  ]) {
    expectResult(wasm, [...leftState, ...rightState], expected);
  }

  // Both signs of zero are admitted by the sign-cleared velocity guard.
  expectResult(
    wasm,
    [bits.one, bits.negativeZero, bits.one, ...right],
    [0n, 0x3fe8800000000000n, 0x3fe199999999999an, 0x3fff800000000000n],
  );

  const valid = [...left, ...right];
  for (const [index, replacement] of [
    [0, bits.eighth - 1n],
    [0, bits.one + 1n],
    [2, bits.sixteenth - 1n],
    [2, bits.one + 1n],
    [1, bits.half + 1n],
    [1, bits.negativeHalf + 1n],
    [3, bits.eighth - 1n],
    [3, bits.one + 1n],
    [5, bits.sixteenth - 1n],
    [5, bits.eighth + 1n],
    [4, bits.half + 1n],
    [4, bits.negativeHalf + 1n],
  ]) {
    const invalid = valid.slice();
    invalid[index] = replacement;
    expectRejected(wasm, invalid);
  }
  expectRejected(wasm, [0x7ff8000000000000n, ...valid.slice(1)]);
  expectRejected(wasm, [valid[0], 0x7ff8000000000000n, ...valid.slice(2)]);

  expectOccurrences("Euler IR", ir, "f64MulBits", 22);
  expectOccurrences("Euler IR", ir, "f64AddBits", 27);
  expectOccurrences("Euler IR", ir, "bitXor", 3);
  expectOccurrences("Euler IR", ir, "LeanExe.Float64.mulBits", 0);
  expectOccurrences("Euler IR", ir, "LeanExe.Float64.addBits", 0);

  const wat = fs.readFileSync(watPath, "utf8");
  const body = exportedFunctionBody(wat, entry);
  expectOccurrences("Euler WAT", body, "f64.mul", 22);
  expectOccurrences("Euler WAT", body, "f64.add", 27);
  expectOccurrences("Euler WAT", body, "i64.xor", 3);
  expectOccurrences("Euler WAT", body, "f64.reinterpret_i64", 98);
  expectOccurrences("Euler WAT", body, "i64.reinterpret_f64", 49);

  process.stdout.write(
    "checked guarded Euler Rusanov Wasmtime results, rejection boundaries, IR, and WAT shape\n",
  );
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
