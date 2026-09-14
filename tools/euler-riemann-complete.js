#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { Readable } = require("node:stream");
const { pipeline } = require("node:stream/promises");
const { createGzip } = require("node:zlib");
const { runCheckedAsync } = require("./run-process");
const { ensureHost } = require("./wasmtime-host");

const root = path.resolve(__dirname, "..");
const digest = "baefc44ed83f46607b7c938a6bc6912fb3fd21442df00c0d0f48c8454bee4310";
const artifact = path.join(root, "proofs/artifacts/euler_riemann", digest, "program.wasm");
const hash = bytes => crypto.createHash("sha256").update(bytes).digest("hex");

function decodeOutput(text, n) {
  text = text.trim();
  if (!text.startsWith("[") || !text.endsWith("]")) throw new Error("invalid array output");
  const words = text.slice(1, -1).split(",").map(word => {
    word = word.trim();
    if (!/^[0-9]+$/.test(word)) throw new Error("invalid output word");
    const value = BigInt(word);
    if (value >= 1n << 64n) throw new Error("output word exceeds UInt64");
    return value;
  });
  if (words.length !== 4 + 2 * n * n) throw new Error("wrong output length");
  const bytes = Buffer.alloc(8 * words.length);
  words.forEach((word, index) => bytes.writeBigUInt64LE(word, 8 * index));
  return bytes;
}

async function writeDataset(directory, n, seconds) {
  const bytes = decodeOutput(fs.readFileSync(path.join(directory, "stdout.txt"), "utf8"), n);
  fs.writeFileSync(path.join(directory, "words.u64le"), bytes, { flag: "wx" });
  const status = bytes.readBigUInt64LE(0);
  if (status !== 0n) throw new Error(`solver returned status ${status}; raw output retained`);
  if (bytes.readBigUInt64LE(8) !== 0x3fe999999999999an) throw new Error("wrong final time");
  if (bytes.readBigUInt64LE(16) !== BigInt(n) || bytes.readBigUInt64LE(24) !== BigInt(n)) {
    throw new Error("wrong output dimensions");
  }
  const density = index => bytes.readDoubleLE(8 * (4 + index));
  const pressure = index => bytes.readDoubleLE(8 * (4 + n * n + index));
  const extrema = { density: [Infinity, -Infinity], pressure: [Infinity, -Infinity] };
  for (let index = 0; index < n * n; index++) {
    for (const [name, value] of [["density", density(index)], ["pressure", pressure(index)]]) {
      if (!Number.isFinite(value) || value <= 0) throw new Error(`invalid ${name} at cell ${index}`);
      extrema[name][0] = Math.min(extrema[name][0], value);
      extrema[name][1] = Math.max(extrema[name][1], value);
    }
  }
  function* rows() {
    yield "i,j,x,y,density,pressure\n";
    for (let index = 0; index < n * n; index++) {
      const i = index % n, j = Math.floor(index / n);
      yield [i, j, (i + 0.5) / n, (j + 0.5) / n, density(index), pressure(index)].join(",") + "\n";
    }
  }
  await pipeline(Readable.from(rows()), createGzip(),
    fs.createWriteStream(path.join(directory, "cells.csv.gz"), { flags: "wx" }));
  const summary = {
    grid: [n, n], domain: [0, 1, 0, 1], initialInterfaces: [0.8, 0.8], time: 0.8,
    status: 0, seconds, artifactSha256: digest, wordsSha256: hash(bytes),
    format: "Little-endian UInt64 words: status, time bits, nx, ny, density bits, pressure bits",
    execution: "One call to the complete solve export in one local Wasmtime process",
    specification: "Project.EulerRiemann.Spec.solve_exact",
    successTheorem: "Project.EulerRiemann.Spec.solve_success",
    artifactExactTheorem: "Project.EulerRiemann.Artifact.artifact_solve_exact",
    artifactSuccessTheorem: "Project.EulerRiemann.Artifact.artifact_solve_success",
    extrema,
  };
  fs.writeFileSync(path.join(directory, "summary.json"), JSON.stringify(summary, null, 2) + "\n", { flag: "wx" });
  console.log(JSON.stringify({ directory, ...summary }));
}

async function main() {
  const [command, grid, output, ...extra] = process.argv.slice(2);
  const n = Number(grid);
  if (command !== "run" || !Number.isInteger(n) || n < 2 || n > 800 || !output || extra.length) {
    throw new Error("usage: euler-riemann-complete.js run <grid-size> <new-directory>");
  }
  if (hash(fs.readFileSync(artifact)) !== digest) throw new Error("artifact digest mismatch");
  const directory = path.resolve(output);
  const host = ensureHost();
  fs.mkdirSync(directory);
  const stdout = fs.openSync(path.join(directory, "stdout.txt"), "wx");
  const stderr = fs.openSync(path.join(directory, "stderr.txt"), "wx");
  const started = performance.now();
  console.log(`Starting complete WASM solve: ${n} x ${n}; output: ${directory}`);
  try {
    await runCheckedAsync([path.join(root, "tools/leanrun"), "--timeout", "24h", host,
      "call", artifact, "solve", "array-u64", `i64:${n}`], {
      cwd: root, stdio: ["ignore", stdout, stderr],
    });
  } finally {
    fs.closeSync(stdout);
    fs.closeSync(stderr);
  }
  await writeDataset(directory, n, (performance.now() - started) / 1000);
}

if (require.main === module) {
  main().catch(error => {
    console.error(error.message);
    process.exitCode = 1;
  });
}

module.exports = { decodeOutput };
