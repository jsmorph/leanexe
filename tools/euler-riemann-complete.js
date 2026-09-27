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
const solvers = {
  run: {
    case: "euler_riemann",
    digest: "baefc44ed83f46607b7c938a6bc6912fb3fd21442df00c0d0f48c8454bee4310",
    module: "Project.EulerRiemann",
  },
  "run-reconstructed": {
    case: "euler_reconstructed",
    digest: "b955d70e023fe830b0a284a3b634923746872e0747b381d697f5b293680362fb",
    module: "Project.EulerReconstructed",
    trials: true,
  },
  "run-certificate": {
    case: "euler_certificate",
    digest: "22696951ce81106990843e19494430292bdde35183058a34ff30133cc47bd981",
    module: "Project.EulerCertificate",
    trials: true,
    certificate: true,
  },
};
const hash = bytes => crypto.createHash("sha256").update(bytes).digest("hex");

function decodeOutput(text, n, certificate = false) {
  text = text.trim();
  if (!text.startsWith("[") || !text.endsWith("]")) throw new Error("invalid array output");
  const words = text.slice(1, -1).split(",").map(word => {
    word = word.trim();
    if (!/^[0-9]+$/.test(word)) throw new Error("invalid output word");
    const value = BigInt(word);
    if (value >= 1n << 64n) throw new Error("output word exceeds UInt64");
    return value;
  });
  if (words.length !== 4 + 2 * n * n + (certificate ? 12 : 0)) throw new Error("wrong output length");
  const bytes = Buffer.alloc(8 * words.length);
  words.forEach((word, index) => bytes.writeBigUInt64LE(word, 8 * index));
  return bytes;
}

async function writeDataset(directory, n, seconds, solver, trials) {
  const bytes = decodeOutput(fs.readFileSync(path.join(directory, "stdout.txt"), "utf8"), n, solver.certificate);
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
  const certificates = solver.certificate ? decodeCertificates(bytes, n) : undefined;
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
    status: 0, seconds, artifactSha256: solver.digest, wordsSha256: hash(bytes),
    ...(trials === undefined ? {} : { reconstructionTrials: trials }),
    format: "Little-endian UInt64 words: status, time bits, nx, ny, density bits, pressure bits" +
      (solver.certificate ? ", then mass, x-momentum, y-momentum, and energy status/lower/upper triples" : ""),
    execution: "One call to the complete solve export in one local Wasmtime process",
    specification: `${solver.module}.Spec.solve_exact`,
    artifactExactTheorem: `${solver.module}.Artifact.artifact_solve_exact`,
    ...(solver.certificate ? {
      enclosureTheorem: `${solver.module}.Spec.solve_enclosure`,
      artifactEnclosureTheorem: `${solver.module}.Artifact.artifact_solve_enclosure`,
      certificates,
    } : {
      successTheorem: `${solver.module}.Spec.solve_success`,
      artifactSuccessTheorem: `${solver.module}.Artifact.artifact_solve_success`,
    }),
    extrema,
  };
  fs.writeFileSync(path.join(directory, "summary.json"), JSON.stringify(summary, null, 2) + "\n", { flag: "wx" });
  console.log(JSON.stringify({ directory, ...summary }));
}

function decodeCertificates(bytes, n) {
  return ["mass", "xMomentum", "yMomentum", "energy"].map((component, index) => {
    const offset = 8 * (4 + 2 * n * n + 3 * index);
    const status = bytes.readBigUInt64LE(offset);
    if (status !== 0n) throw new Error(`${component} certificate returned status ${status}; raw output retained`);
    const lower = bytes.readDoubleLE(offset + 8), upper = bytes.readDoubleLE(offset + 16);
    if (!Number.isFinite(lower) || !Number.isFinite(upper) || lower > upper) {
      throw new Error(`invalid ${component} certificate endpoints; raw output retained`);
    }
    return {
      component, status: 0,
      lowerBits: bytes.readBigUInt64LE(offset + 8).toString(),
      upperBits: bytes.readBigUInt64LE(offset + 16).toString(),
      lower, upper, absoluteBound: Math.max(-lower, upper), approximateWidth: upper - lower,
    };
  });
}

async function main() {
  const [command, grid, ...args] = process.argv.slice(2);
  const solver = Object.hasOwn(solvers, command) ? solvers[command] : undefined;
  const [trials, output, ...extra] = solver?.trials ? args : [undefined, ...args];
  const n = Number(grid);
  if (!solver || !Number.isInteger(n) || n < 2 || n > 800 || !output || extra.length ||
      (solver.trials && (!/^(0|[1-9][0-9]*)$/.test(trials) || BigInt(trials) >= 1n << 64n))) {
    throw new Error("usage: euler-riemann-complete.js run <grid-size> <new-directory> | run-reconstructed <grid-size> <trials> <new-directory> | run-certificate <grid-size> <trials> <new-directory>");
  }
  const artifact = path.join(root, "proofs/artifacts", solver.case, solver.digest, "program.wasm");
  if (hash(fs.readFileSync(artifact)) !== solver.digest) throw new Error("artifact digest mismatch");
  const directory = path.resolve(output);
  const host = ensureHost();
  fs.mkdirSync(directory);
  const stdout = fs.openSync(path.join(directory, "stdout.txt"), "wx");
  const stderr = fs.openSync(path.join(directory, "stderr.txt"), "wx");
  const started = performance.now();
  console.log(`Starting complete WASM solve: ${solver.case}, ${n} x ${n}; output: ${directory}`);
  try {
    await runCheckedAsync([path.join(root, "tools/leanrun"), "--timeout", "24h", host,
      "call", artifact, "solve", "array-u64", `i64:${n}`, ...(solver.trials ? [`i64:${trials}`] : [])], {
      cwd: root, stdio: ["ignore", stdout, stderr],
    });
  } finally {
    fs.closeSync(stdout);
    fs.closeSync(stderr);
  }
  await writeDataset(directory, n, (performance.now() - started) / 1000, solver, trials);
}

if (require.main === module) {
  main().catch(error => {
    console.error(error.message);
    process.exitCode = 1;
  });
}

module.exports = { decodeOutput, decodeCertificates };
