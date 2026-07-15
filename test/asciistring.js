#!/usr/bin/env node

const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const moduleName = "LeanExe.Examples.AsciiStringPrograms";
const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "asciistring-programs");

function run(args) {
  return runChecked(args, { encoding: "utf8" });
}

function compile(entry) {
  const out = path.join(outDir, `${entry}.wasm`);
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
  return out;
}

function instantiate(entry) {
  return { entry, wasm: compile(entry) };
}

function callScalar(exports, input) {
  return host.callI64(exports.wasm, exports.entry, [host.byteArray(input)]);
}

function callByteArray(exports, input) {
  return host.callBytes(exports.wasm, exports.entry, [host.byteArray(input)]);
}

function callScalarNoArgs(exports) {
  return host.callI64(exports.wasm, exports.entry);
}

function callByteArrayWithArgs(exports, input, args) {
  return host.callBytes(exports.wasm, exports.entry, [
    host.byteArray(input),
    ...args.map((arg) => host.i64(arg)),
  ]);
}

function bytes(text) {
  return new TextEncoder().encode(text);
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

async function main() {
  run(["lake", "build", moduleName]);
  fs.mkdirSync(outDir, { recursive: true });

  const validAscii = await instantiate("validAscii");
  const checkedSize = await instantiate("checkedSize");
  const firstOrQuestion = await instantiate("firstOrQuestion");
  const identityTrusted = await instantiate("identityTrusted");
  const appendBangOrQuestion = await instantiate("appendBangOrQuestion");
  const pushIfAscii = await instantiate("pushIfAscii");
  const appendSelfTrusted = await instantiate("appendSelfTrusted");
  const prefixBangTrusted = await instantiate("prefixBangTrusted");
  const middle = await instantiate("middle");
  const equalsABC = await instantiate("equalsABC");
  const startsWithAB = await instantiate("startsWithAB");
  const containsColon = await instantiate("containsColon");
  const trustedStringLength = await instantiate("trustedStringLength");

  const ascii = bytes("AZ09");
  const invalid = new Uint8Array([65, 128, 66]);

  if (callScalar(validAscii, ascii) !== 1n || callScalar(validAscii, invalid) !== 0n) {
    throw new Error("validAscii: unexpected result");
  }

  if (callScalar(checkedSize, ascii) !== 4n || callScalar(checkedSize, invalid) !== 0n) {
    throw new Error("checkedSize: unexpected result");
  }

  if (callScalar(firstOrQuestion, bytes("Hi")) !== 72n || callScalar(firstOrQuestion, invalid) !== 63n) {
    throw new Error("firstOrQuestion: unexpected result");
  }

  expectBytes("identityTrusted", callByteArray(identityTrusted, bytes("id")), bytes("id"));
  expectBytes("appendBangOrQuestion ascii", callByteArray(appendBangOrQuestion, bytes("OK")), bytes("OK!"));
  expectBytes("appendBangOrQuestion invalid", callByteArray(appendBangOrQuestion, invalid), bytes("?"));
  expectBytes("pushIfAscii valid", callByteArrayWithArgs(pushIfAscii, bytes("A"), [66n]), bytes("AB"));
  expectBytes("pushIfAscii invalid byte", callByteArrayWithArgs(pushIfAscii, bytes("A"), [200n]), new Uint8Array([]));
  expectBytes("appendSelfTrusted", callByteArray(appendSelfTrusted, bytes("ab")), bytes("abab"));
  expectBytes("prefixBangTrusted", callByteArray(prefixBangTrusted, bytes("go")), bytes("!go"));
  expectBytes("middle ascii", callByteArray(middle, bytes("abcd")), bytes("bc"));
  expectBytes("middle invalid", callByteArray(middle, invalid), new Uint8Array([]));

  if (
    callScalar(equalsABC, bytes("abc")) !== 1n ||
    callScalar(equalsABC, bytes("abd")) !== 0n ||
    callScalar(equalsABC, bytes("abcd")) !== 0n
  ) {
    throw new Error("equalsABC: unexpected result");
  }

  if (
    callScalar(startsWithAB, bytes("abc")) !== 1n ||
    callScalar(startsWithAB, bytes("a")) !== 0n ||
    callScalar(startsWithAB, invalid) !== 0n
  ) {
    throw new Error("startsWithAB: unexpected result");
  }

  if (callScalar(containsColon, bytes("a:b")) !== 1n || callScalar(containsColon, bytes("abc")) !== 0n) {
    throw new Error("containsColon: unexpected result");
  }

  if (callScalarNoArgs(trustedStringLength) !== 4n) {
    throw new Error("trustedStringLength: unexpected result");
  }

  process.stdout.write("checked 23 asciistring cases\n");
}

main().catch((error) => {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
});
