#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { runChecked, spawnResult } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.Float64Bits";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "f64-bits");

function run(args) {
  return runChecked(args, { encoding: "utf8" }).stdout;
}

function sourceEntry(entry) {
  return `${moduleName}.${entry}`;
}

function compile(entry, annotations = null) {
  const wasm = path.join(outDir, `${entry}.wasm`);
  const args = [
    leanExe,
    "compile",
    "--module",
    moduleName,
    "--entry",
    sourceEntry(entry),
    "--out",
    wasm,
  ];
  if (annotations !== null) {
    args.push("--annotations", annotations);
  }
  run(args);
  return wasm;
}

function compileWat(entry) {
  const wat = path.join(outDir, `${entry}.wat`);
  run([
    leanExe,
    "compile-wat",
    "--module",
    moduleName,
    "--entry",
    sourceEntry(entry),
    "--out",
    wat,
  ]);
  return fs.readFileSync(wat, "utf8");
}

function dumpIr(entry) {
  return run([
    leanExe,
    "dump-ir",
    "--module",
    moduleName,
    "--entry",
    sourceEntry(entry),
  ]);
}

function report(entry) {
  return run([
    leanExe,
    "report",
    "--module",
    moduleName,
    "--entry",
    sourceEntry(entry),
  ]);
}

function occurrences(text, fragment) {
  let count = 0;
  let offset = 0;
  while (true) {
    const next = text.indexOf(fragment, offset);
    if (next < 0) return count;
    count += 1;
    offset = next + fragment.length;
  }
}

function expectOccurrences(label, text, fragment, expected) {
  const actual = occurrences(text, fragment);
  if (actual !== expected) {
    throw new Error(`${label}: expected ${expected} occurrences of ${fragment}, got ${actual}`);
  }
}

function expectBits(wasm, entry, args, expected) {
  const actual = host.callI64(wasm, entry, args.map(host.i64));
  if (actual !== expected) {
    const inputs = args.map((value) => `0x${value.toString(16).padStart(16, "0")}`).join(", ");
    throw new Error(
      `${entry}(${inputs}): expected 0x${expected.toString(16).padStart(16, "0")}, ` +
        `got 0x${actual.toString(16).padStart(16, "0")}`,
    );
  }
}

function expectSlots(wasm, entry, args, expected) {
  const output = host.call(wasm, entry, `slots:${expected.length}`, args.map(host.i64));
  const actual = output.split(/\s+/).filter(Boolean).map((value) =>
    BigInt.asUintN(64, BigInt(value)));
  if (actual.length !== expected.length || actual.some((value, index) => value !== expected[index])) {
    throw new Error(`${entry}: expected slots ${expected}, got ${actual}`);
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

function exportedInstructions(wat, exportName) {
  const lines = exportedFunctionBody(wat, exportName)
    .trim()
    .split(/\r?\n/)
    .map((line) => line.trim());
  if (!lines[0].startsWith("(func ") || lines[lines.length - 1] !== ")") {
    throw new Error(`${exportName}: malformed WAT function body`);
  }
  return lines.slice(1, -1).filter((line) => !line.startsWith("(local"));
}

function expectInstructions(entry, actual, expected) {
  if (actual.length !== expected.length || actual.some((line, index) => line !== expected[index])) {
    throw new Error(
      `${entry}: unexpected WAT instructions\nactual:   ${actual.join(" | ")}\n` +
        `expected: ${expected.join(" | ")}`,
    );
  }
}

function countByteSequence(bytes, sequence) {
  const needle = Buffer.from(sequence);
  let count = 0;
  let offset = 0;
  while (true) {
    const next = bytes.indexOf(needle, offset);
    if (next < 0) return count;
    count += 1;
    offset = next + 1;
  }
}

function expectByteSequence(entry, wasm, sequence) {
  const count = countByteSequence(fs.readFileSync(wasm), sequence);
  if (count !== 1) {
    const hex = sequence.map((byte) => byte.toString(16).padStart(2, "0")).join(" ");
    throw new Error(`${entry}: expected one raw instruction sequence ${hex}, got ${count}`);
  }
}

function checkAnnotations(wasm, annotationsPath, entry, parameterCount) {
  const annotations = JSON.parse(fs.readFileSync(annotationsPath, "utf8"));
  const byteLength = fs.statSync(wasm).size;
  if (annotations.schemaVersion !== 1 || annotations.artifact?.byteLength !== byteLength) {
    throw new Error(`${entry}: annotation artifact metadata does not match the ${byteLength}-byte module`);
  }
  const func = annotations.functions?.find((item) => item.sourceName === sourceEntry(entry));
  if (
    !func ||
    func.parameters !== parameterCount ||
    func.results !== 1 ||
    !func.exports?.includes(entry) ||
    !Array.isArray(func.regions)
  ) {
    throw new Error(`${entry}: annotations do not describe the expected UInt64-bit ABI`);
  }
}

function checkImageRejection(entry) {
  const image = path.join(outDir, `${entry}.image`);
  fs.rmSync(image, { force: true });
  const result = spawnResult(
    [
      leanExe,
      "compile-image",
      "--module",
      moduleName,
      "--entry",
      sourceEntry(entry),
      "--out",
      image,
    ],
    { encoding: "utf8" },
  );
  const output = `${result.stdout}\n${result.stderr}`;
  if (result.status !== 5) {
    throw new Error(`${entry}: compile-image should fail with internal status 5, got ${result.status}\n${output}`);
  }
  for (const fragment of ["lean-wasm: internal", 'command "compile-image"', "image schema v2", "f64"]) {
    if (!output.includes(fragment)) {
      throw new Error(`${entry}: compile-image failure is missing ${JSON.stringify(fragment)}\n${output}`);
    }
  }
  if (fs.existsSync(image)) {
    throw new Error(`${entry}: compile-image left an output despite rejecting f64 instructions`);
  }
}

function main() {
  fs.mkdirSync(outDir, { recursive: true });

  const annotationsPath = path.join(outDir, "addBits.annotations.json");
  const addWasm = compile("addBits", annotationsPath);
  const mulWasm = compile("mulBits");
  const mulThenAddWasm = compile("mulThenAddBits");
  const addMulWasm = compile("addMulBits");
  const dot2Wasm = compile("dot2CheckedBits");
  const horner2Wasm = compile("horner2CheckedBits");

  for (const [left, right, expected] of [
    [0x3ff8000000000000n, 0x4002000000000000n, 0x400e000000000000n],
    [0xbff8000000000000n, 0x3fe0000000000000n, 0xbff0000000000000n],
  ]) {
    expectBits(addWasm, "addBits", [left, right], expected);
  }
  for (const [left, right, expected] of [
    [0x3ff8000000000000n, 0x4000000000000000n, 0x4008000000000000n],
    [0x8000000000000000n, 0x4000000000000000n, 0x8000000000000000n],
    [0x0000000000000001n, 0x3ff0000000000000n, 0x0000000000000001n],
  ]) {
    expectBits(mulWasm, "mulBits", [left, right], expected);
  }
  expectBits(
    mulThenAddWasm,
    "mulThenAddBits",
    [0x3ff8000000000000n, 0x4000000000000000n, 0x3fe8000000000000n],
    0x400e000000000000n,
  );
  expectSlots(
    dot2Wasm,
    "dot2CheckedBits",
    [0x3fe0000000000000n, 0x3fe0000000000000n,
      0x3fd0000000000000n, 0x3fe0000000000000n],
    [0n, 0x3fd8000000000000n],
  );
  expectSlots(
    dot2Wasm,
    "dot2CheckedBits",
    [0x3fe0000000000000n, 0x3fe0000000000000n,
      0xbfe0000000000000n, 0x3fe0000000000000n],
    [0n, 0n],
  );
  expectSlots(
    dot2Wasm,
    "dot2CheckedBits",
    [0x3ff0000000000000n, 0x3fe0000000000000n,
      0n, 0n],
    [1n, 0n],
  );
  expectSlots(
    horner2Wasm,
    "horner2CheckedBits",
    [0x3fe0000000000000n, 0x3fe0000000000000n,
      0x3fd0000000000000n, 0xbfe0000000000000n],
    [0n, 0xbfd0000000000000n],
  );
  expectSlots(
    horner2Wasm,
    "horner2CheckedBits",
    [0xbfe0000000000000n, 0x3fe0000000000000n,
      0x3fe0000000000000n, 0x3fe0000000000000n],
    [0n, 0x3fd8000000000000n],
  );
  for (const args of [
    [0x3fe0000000000001n, 0n, 0n, 0n],
    [0n, 0xbfe0000000000001n, 0n, 0n],
    [0n, 0n, 0x7ff8000000000000n, 0n],
    [0n, 0n, 0n, 0x7ff0000000000000n],
  ]) {
    expectSlots(horner2Wasm, "horner2CheckedBits", args, [1n, 0n]);
  }
  expectBits(
    addMulWasm,
    "addMulBits",
    [0x3fe8000000000000n, 0x3ff8000000000000n, 0x4000000000000000n],
    0x400e000000000000n,
  );

  const addIr = dumpIr("addBits");
  expectOccurrences("addBits IR", addIr, "f64AddBits", 1);
  expectOccurrences("addBits IR", addIr, "f64MulBits", 0);
  const mulIr = dumpIr("mulBits");
  expectOccurrences("mulBits IR", mulIr, "f64AddBits", 0);
  expectOccurrences("mulBits IR", mulIr, "f64MulBits", 1);
  const nestedIr = dumpIr("mulThenAddBits");
  expectOccurrences("mulThenAddBits IR", nestedIr, "f64AddBits", 1);
  expectOccurrences("mulThenAddBits IR", nestedIr, "f64MulBits", 1);
  const rightNestedIr = dumpIr("addMulBits");
  expectOccurrences("addMulBits IR", rightNestedIr, "f64AddBits", 1);
  expectOccurrences("addMulBits IR", rightNestedIr, "f64MulBits", 1);
  const dot2Ir = dumpIr("dot2CheckedBits");
  expectOccurrences("dot2CheckedBits IR", dot2Ir, "f64AddBits", 1);
  expectOccurrences("dot2CheckedBits IR", dot2Ir, "f64MulBits", 2);
  const horner2Ir = dumpIr("horner2CheckedBits");
  expectOccurrences("horner2CheckedBits IR", horner2Ir, "f64AddBits", 2);
  expectOccurrences("horner2CheckedBits IR", horner2Ir, "f64MulBits", 2);
  for (const [entry, ir] of [
    ["addBits", addIr],
    ["mulBits", mulIr],
    ["mulThenAddBits", nestedIr],
    ["addMulBits", rightNestedIr],
    ["dot2CheckedBits", dot2Ir],
    ["horner2CheckedBits", horner2Ir],
  ]) {
    if (ir.includes("LeanExe.Float64.addBits") || ir.includes("LeanExe.Float64.mulBits")) {
      throw new Error(`${entry}: intrinsic call survived in the lowered IR`);
    }
  }

  const nestedReport = report("mulThenAddBits");
  for (const intrinsic of ["LeanExe.Float64.addBits", "LeanExe.Float64.mulBits"]) {
    if (!nestedReport.includes(intrinsic) ||
        !nestedReport.includes("compiler-recognized UInt64 bit-pattern floating-point intrinsic")) {
      throw new Error(`mulThenAddBits: report does not classify ${intrinsic} as implemented`);
    }
  }
  if (nestedReport.includes("Float.toBits") || nestedReport.includes("Float.ofBits")) {
    throw new Error("mulThenAddBits: native Float implementation leaked past the intrinsic boundary");
  }

  expectInstructions("addBits", exportedInstructions(compileWat("addBits"), "addBits"), [
    "local.get 0",
    "f64.reinterpret_i64",
    "local.get 1",
    "f64.reinterpret_i64",
    "f64.add",
    "i64.reinterpret_f64",
    "local.set 2",
    "local.get 2",
  ]);
  expectInstructions("mulBits", exportedInstructions(compileWat("mulBits"), "mulBits"), [
    "local.get 0",
    "f64.reinterpret_i64",
    "local.get 1",
    "f64.reinterpret_i64",
    "f64.mul",
    "i64.reinterpret_f64",
    "local.set 2",
    "local.get 2",
  ]);
  expectInstructions(
    "mulThenAddBits",
    exportedInstructions(compileWat("mulThenAddBits"), "mulThenAddBits"),
    [
      "local.get 0",
      "f64.reinterpret_i64",
      "local.get 1",
      "f64.reinterpret_i64",
      "f64.mul",
      "i64.reinterpret_f64",
      "f64.reinterpret_i64",
      "local.get 2",
      "f64.reinterpret_i64",
      "f64.add",
      "i64.reinterpret_f64",
      "local.set 3",
      "local.get 3",
    ],
  );
  expectInstructions("addMulBits", exportedInstructions(compileWat("addMulBits"), "addMulBits"), [
    "local.get 0",
    "f64.reinterpret_i64",
    "local.get 1",
    "f64.reinterpret_i64",
    "local.get 2",
    "f64.reinterpret_i64",
    "f64.mul",
    "i64.reinterpret_f64",
    "f64.reinterpret_i64",
    "f64.add",
    "i64.reinterpret_f64",
    "local.set 3",
    "local.get 3",
  ]);
  const dot2Wat = exportedFunctionBody(compileWat("dot2CheckedBits"), "dot2CheckedBits");
  expectOccurrences("dot2CheckedBits WAT", dot2Wat, "f64.mul", 2);
  expectOccurrences("dot2CheckedBits WAT", dot2Wat, "f64.add", 1);
  expectOccurrences("dot2CheckedBits WAT", dot2Wat, "f64.reinterpret_i64", 6);
  expectOccurrences("dot2CheckedBits WAT", dot2Wat, "i64.reinterpret_f64", 3);
  const horner2Wat = exportedFunctionBody(compileWat("horner2CheckedBits"), "horner2CheckedBits");
  expectOccurrences("horner2CheckedBits WAT", horner2Wat, "f64.mul", 2);
  expectOccurrences("horner2CheckedBits WAT", horner2Wat, "f64.add", 2);
  expectOccurrences("horner2CheckedBits WAT", horner2Wat, "f64.reinterpret_i64", 8);
  expectOccurrences("horner2CheckedBits WAT", horner2Wat, "i64.reinterpret_f64", 4);

  expectByteSequence("addBits", addWasm, [
    0x20, 0x00, 0xbf, 0x20, 0x01, 0xbf, 0xa0, 0xbd, 0x21, 0x02, 0x20, 0x02, 0x0b,
  ]);
  expectByteSequence("mulBits", mulWasm, [
    0x20, 0x00, 0xbf, 0x20, 0x01, 0xbf, 0xa2, 0xbd, 0x21, 0x02, 0x20, 0x02, 0x0b,
  ]);
  expectByteSequence("mulThenAddBits", mulThenAddWasm, [
    0x20, 0x00, 0xbf,
    0x20, 0x01, 0xbf,
    0xa2, 0xbd, 0xbf,
    0x20, 0x02, 0xbf,
    0xa0, 0xbd,
    0x21, 0x03,
    0x20, 0x03,
    0x0b,
  ]);
  expectByteSequence("addMulBits", addMulWasm, [
    0x20, 0x00, 0xbf,
    0x20, 0x01, 0xbf,
    0x20, 0x02, 0xbf,
    0xa2, 0xbd, 0xbf,
    0xa0, 0xbd,
    0x21, 0x03,
    0x20, 0x03,
    0x0b,
  ]);

  checkAnnotations(addWasm, annotationsPath, "addBits", 2);
  checkImageRejection("mulThenAddBits");

  process.stdout.write("checked Float64 bit-pattern execution, lowering, emission, annotations, and image rejection\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
