#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "json-programs");

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(result.stderr.trim() || result.stdout.trim() || `${args[0]} failed`);
  }
  return result;
}

async function instantiate(moduleName) {
  fs.mkdirSync(outDir, { recursive: true });
  const parts = moduleName.split(".");
  const out = path.join(outDir, `${parts[parts.length - 1]}.wasm`);
  const entryName = `${moduleName}.transform`;
  run([leanExe, "compile", "--module", moduleName, "--entry", entryName, "--out", out]);
  const wasm = fs.readFileSync(out);
  const { instance } = await WebAssembly.instantiate(wasm, {});
  const { memory, alloc, reset, transform } = instance.exports;
  if (!memory || typeof alloc !== "function" || typeof reset !== "function") {
    throw new Error("compiled module does not export memory, alloc, and reset");
  }
  if (typeof transform !== "function") {
    throw new Error("compiled module does not export transform");
  }
  return { memory, alloc, reset, transform };
}

function bytes(text) {
  return new TextEncoder().encode(text);
}

function writeInput(exports, input) {
  exports.reset();
  const ptr = Number(exports.alloc(BigInt(input.length)));
  new Uint8Array(exports.memory.buffer, ptr, input.length).set(input);
  return [BigInt(ptr), BigInt(input.length)];
}

function readByteArrayResult(exports, result) {
  if (!Array.isArray(result) || result.length !== 2) {
    throw new Error(`expected ByteArray result, got ${result}`);
  }
  const ptr = Number(BigInt.asUintN(64, result[0]));
  const len = Number(BigInt.asUintN(64, result[1]));
  return Uint8Array.from(new Uint8Array(exports.memory.buffer, ptr, len));
}

function sameBytes(left, right) {
  if (left.length !== right.length) {
    return false;
  }
  for (let index = 0; index < left.length; index += 1) {
    if (left[index] !== right[index]) {
      return false;
    }
  }
  return true;
}

function expectBytes(name, actual, expected) {
  if (!sameBytes(actual, expected)) {
    throw new Error(`${name}: expected ${Array.from(expected)}, got ${Array.from(actual)}`);
  }
}

function callTransform(exports, input) {
  const args = writeInput(exports, input);
  return readByteArrayResult(exports, exports.transform(...args));
}

async function main() {
  const doubleModule = "LeanExe.Examples.JsonDouble";
  const addModule = "LeanExe.Examples.JsonAdd";
  const collatzModule = "LeanExe.Examples.JsonCollatzLength";
  run(["lake", "build", doubleModule]);
  run(["lake", "build", addModule]);
  run(["lake", "build", collatzModule]);
  const doubleExports = await instantiate(doubleModule);
  const addExports = await instantiate(addModule);
  const collatzExports = await instantiate(collatzModule);
  const error = bytes('{"error":1}');
  const doubleCases = [
    ["zero", bytes('{"n":0}'), bytes('{"result":0}')],
    ["simple", bytes('{"n":21}'), bytes('{"result":42}')],
    ["whitespace", bytes(' { "n" : 7 } '), bytes('{"result":14}')],
    ["leading zeros", bytes('{"n":00012}'), bytes('{"result":24}')],
    [
      "largest double",
      bytes('{"n":9223372036854775807}'),
      bytes('{"result":18446744073709551614}'),
    ],
    ["double overflow", bytes('{"n":9223372036854775808}'), error],
    ["parse overflow", bytes('{"n":18446744073709551616}'), error],
    ["wrong key", bytes('{"m":1}'), error],
    ["missing digits", bytes('{"n":}'), error],
    ["negative", bytes('{"n":-1}'), error],
    ["trailing junk", bytes('{"n":1}x'), error],
    ["non-ascii", new Uint8Array([123, 34, 110, 34, 58, 49, 200, 125]), error],
  ];
  const addCases = [
    ["add zero", bytes('{"a":0,"b":0}'), bytes('{"sum":0}')],
    ["add simple", bytes('{"a":19,"b":23}'), bytes('{"sum":42}')],
    ["add whitespace", bytes(' { "a" : 7 , "b" : 35 } '), bytes('{"sum":42}')],
    [
      "add max",
      bytes('{"a":18446744073709551615,"b":0}'),
      bytes('{"sum":18446744073709551615}'),
    ],
    ["add overflow", bytes('{"a":18446744073709551615,"b":1}'), error],
    ["add parse overflow", bytes('{"a":18446744073709551616,"b":0}'), error],
    ["add wrong order", bytes('{"b":1,"a":2}'), error],
    ["add missing comma", bytes('{"a":1 "b":2}'), error],
    ["add trailing junk", bytes('{"a":1,"b":2}x'), error],
    ["add non-ascii", new Uint8Array([123, 34, 97, 34, 58, 49, 44, 34, 98, 34, 58, 50, 200, 125]), error],
  ];
  const collatzCases = [
    ["collatz 41", bytes('{"collatzLengthFor":41}'), bytes('{"length":110}')],
    ["collatz one", bytes('{"collatzLengthFor":1}'), bytes('{"length":1}')],
    ["collatz whitespace", bytes(' { "collatzLengthFor" : 7 } '), bytes('{"length":17}')],
    ["collatz zero", bytes('{"collatzLengthFor":0}'), error],
    ["collatz parse overflow", bytes('{"collatzLengthFor":18446744073709551616}'), error],
    ["collatz step overflow", bytes('{"collatzLengthFor":18446744073709551615}'), error],
    ["collatz wrong key", bytes('{"n":41}'), error],
    ["collatz trailing junk", bytes('{"collatzLengthFor":41}x'), error],
    ["collatz non-ascii", new Uint8Array([123, 34, 99, 111, 108, 108, 97, 116, 122, 76, 101, 110, 103, 116, 104, 70, 111, 114, 34, 58, 52, 49, 200, 125]), error],
  ];

  for (const testCase of doubleCases) {
    expectBytes(testCase[0], callTransform(doubleExports, testCase[1]), testCase[2]);
  }
  for (const testCase of addCases) {
    expectBytes(testCase[0], callTransform(addExports, testCase[1]), testCase[2]);
  }
  for (const testCase of collatzCases) {
    expectBytes(testCase[0], callTransform(collatzExports, testCase[1]), testCase[2]);
  }

  process.stdout.write(`checked ${doubleCases.length + addCases.length + collatzCases.length} json program cases\n`);
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
