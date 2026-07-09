#!/usr/bin/env node

// The self-compilation fixed point for the LEB128 core: the compiler's own
// encoder, compiled by the compiler to WASM, must produce the same bytes as
// an independent reference over the encoding domain's boundary values.

const fs = require("fs");
const path = require("path");
const { spawnSync } = require("child_process");
const host = require("./wasmtime_host");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "self-emit");
const moduleName = "LeanExe.Wasm.Leb";

function run(args) {
  const result = spawnSync(args[0], args.slice(1), { encoding: "utf8" });
  if (result.status !== 0) {
    throw new Error(`${args.join(" ")} failed:\n${result.stdout}\n${result.stderr}`);
  }
}

function compile(entry) {
  fs.mkdirSync(outDir, { recursive: true });
  const out = path.join(outDir, `${entry}.wasm`);
  run([leanExe, "compile", "--module", moduleName, "--entry", `${moduleName}.${entry}`, "--out", out]);
  return out;
}

function u32lebRef(value) {
  let v = BigInt(value);
  const out = [];
  for (;;) {
    const low = v % 128n;
    const rest = v / 128n;
    if (rest === 0n) {
      out.push(Number(low));
      return Uint8Array.from(out);
    }
    out.push(Number(low + 128n));
    v = rest;
  }
}

function s64lebRef(bits) {
  let v = BigInt.asIntN(64, BigInt(bits));
  const out = [];
  for (;;) {
    const low = v & 0x7fn;
    const rest = v >> 7n;
    if ((rest === 0n && (low & 0x40n) === 0n) || (rest === -1n && (low & 0x40n) !== 0n)) {
      out.push(Number(low));
      return Uint8Array.from(out);
    }
    out.push(Number(low + 128n));
    v = rest;
  }
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

function check(wasm, entry, ref, corpus) {
  let total = 0;
  for (const value of corpus) {
    const actual = host.callBytes(wasm, entry, [host.i64(value)]);
    const expected = ref(value);
    if (!sameBytes(actual, expected)) {
      throw new Error(
        `${entry}(${value}): artifact [${Array.from(actual)}] != reference [${Array.from(expected)}]`);
    }
    total += 1;
  }
  return total;
}

function main() {
  const unsignedCorpus = [
    0n, 1n, 63n, 64n, 127n, 128n, 129n, 16383n, 16384n,
    (1n << 21n) - 1n, 1n << 21n, (1n << 28n) - 1n, 1n << 28n,
    (1n << 32n) - 1n, 1n << 32n, (1n << 35n) - 1n,
    (1n << 56n) - 1n, 1n << 56n, (1n << 63n) - 1n, 1n << 63n,
    (1n << 64n) - 1n,
  ];
  const signedBitsCorpus = [
    0n, 1n, 63n, 64n, 127n, 128n, 8191n, 8192n,
    (1n << 62n) - 1n, 1n << 62n, (1n << 63n) - 1n,
    1n << 63n,
    (1n << 64n) - 1n, (1n << 64n) - 64n, (1n << 64n) - 65n,
    (1n << 64n) - 128n, (1n << 64n) - 8192n, (1n << 64n) - 8193n,
  ];
  const u32leb = compile("u32lebU64");
  const s64leb = compile("s64lebU64");
  let total = 0;
  total += check(u32leb, "u32lebU64", u32lebRef, unsignedCorpus);
  total += check(s64leb, "s64lebU64", s64lebRef, signedBitsCorpus);

  // The vector and section combinators with host-marshalable signatures.
  // The array-input combinators (vecBytes, u32VecBytes) are exercised
  // natively on every compile, since the native encoder calls them for
  // every emitted module and the Talos artifact checks pin those bytes.
  const byteCorpus = [
    new Uint8Array([]),
    new Uint8Array([0]),
    new Uint8Array([1, 2, 3]),
    new Uint8Array(Array.from({ length: 127 }, (_, i) => i % 256)),
    new Uint8Array(Array.from({ length: 128 }, (_, i) => (i * 7) % 256)),
    new Uint8Array(Array.from({ length: 300 }, (_, i) => (i * 13) % 256)),
  ];
  const byteVec = compile("byteVecBytes");
  for (const bytes of byteCorpus) {
    const actual = host.callBytes(byteVec, "byteVecBytes", [host.byteArray(bytes)]);
    const expected = Uint8Array.from([...u32lebRef(bytes.length), ...bytes]);
    if (!sameBytes(actual, expected)) {
      throw new Error(`byteVecBytes(${bytes.length} bytes): mismatch`);
    }
    total += 1;
  }
  const section = compile("sectionBytes");
  for (const bytes of byteCorpus) {
    for (const id of [1n, 10n, 11n]) {
      const actual = host.callBytes(section, "sectionBytes", [host.i64(id), host.byteArray(bytes)]);
      const expected = Uint8Array.from([Number(id), ...u32lebRef(bytes.length), ...bytes]);
      if (!sameBytes(actual, expected)) {
        throw new Error(`sectionBytes(${id}, ${bytes.length} bytes): mismatch`);
      }
      total += 1;
    }
  }
  process.stdout.write(`checked ${total} self-emitted LEB128 cases\n`);
}

main();
