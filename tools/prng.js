#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { spawnResult } = require("./run-process");
const { ensureHost, i64Argument, maxUInt64 } = require("./wasmtime-host");

const root = path.resolve(__dirname, "..");
const moduleName = "LeanExe.Examples.Prng";
const wasm = path.join(root, "build/prng/prng.wasm");
const usage = "usage: tools/prng.js SEED N MODULUS\n" +
  "Unsigned decimal inputs. MODULUS must be positive. Prints N decimal integers, one per line.\n";
let prepared = false;

function uint64(text, name) {
  if (typeof text !== "string" || !/^[0-9]+$/.test(text) || BigInt(text) > maxUInt64) {
    throw new RangeError(`${name} must be an unsigned decimal integer in [0, ${maxUInt64}]`);
  }
  return BigInt(text);
}

function run(args, options) {
  const result = spawnResult(args, options);
  if (result.status !== 0) {
    const detail = [result.stderr, result.stdout].map(text => (text || "").trim())
      .filter(Boolean).join("\n");
    const reason = result.signal ? `terminated by ${result.signal}` : `exited with status ${result.status}`;
    const error = new Error(`${path.basename(args[0])} ${reason}${detail ? `:\n${detail}` : ""}`);
    error.exitCode = result.status || 1;
    throw error;
  }
  return result;
}

function prepare() {
  if (prepared) return;
  run(["lake", "build", "lean-wasm", moduleName],
    { cwd: root, encoding: "utf8", timeout: 900000 });
  fs.mkdirSync(path.dirname(wasm), { recursive: true });
  run([path.join(root, ".lake/build/bin/lean-wasm"), "compile",
    "--module", moduleName, "--entry", `${moduleName}.generate`, "--out", wasm],
    { cwd: root, encoding: "utf8", timeout: 120000 });
  prepared = true;
}

function runPrng(seedText, countText, modulusText) {
  const seed = uint64(seedText, "SEED");
  const count = uint64(countText, "N");
  const modulus = uint64(modulusText, "MODULUS");
  if (modulus === 0n) throw new RangeError("MODULUS must be positive");
  prepare();
  const output = run([ensureHost(), "call", wasm, "generate", "array-u64",
    ...[seed, count, modulus].map(i64Argument)],
    { cwd: root, encoding: "utf8", timeout: 60000, maxBuffer: 64 * 1024 * 1024 }).stdout.trim();
  if (!/^\[(?:[0-9]+(?:, [0-9]+)*)?\]$/.test(output)) {
    throw new Error("Wasmtime returned an invalid UInt64 array");
  }
  const words = output === "[]" ? [] : output.slice(1, -1).split(", ");
  if (BigInt(words.length) !== count || words.some(word => BigInt(word) >= modulus)) {
    throw new Error("Wasmtime returned the wrong count or a value outside [0, MODULUS)");
  }
  return words;
}

function main(args) {
  if (args.length === 1 && args[0] === "--help") {
    process.stdout.write(usage);
    return;
  }
  if (args.length !== 3) throw new RangeError(usage.trim());
  const words = runPrng(...args);
  if (words.length > 0) process.stdout.write(`${words.join("\n")}\n`);
}

if (require.main === module) {
  try { main(process.argv.slice(2)); }
  catch (error) {
    process.stderr.write(`prng: ${error.message}\n`);
    process.exitCode = error instanceof RangeError ? 2 : (error.exitCode || 1);
  }
}

module.exports = { runPrng };
