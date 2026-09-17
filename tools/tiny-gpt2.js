#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { runChecked } = require("./run-process");
const { ensureHost, i64Argument, maxUInt64 } = require("./wasmtime-host");

const root = path.resolve(__dirname, "..");
const directory = path.join(root, "data/tiny-gpt2-v1");
const names = ["token", "position", "query", "key", "value", "attention", "attention_bias",
  "expand", "expand_bias", "contract", "contract_bias", "head", "head_bias",
  "norm1_scale", "norm1_bias", "norm2_scale", "norm2_bias", "norm_final_scale", "norm_final_bias"];

function checkedFile(name, digest) {
  const bytes = fs.readFileSync(path.join(directory, name));
  if (crypto.createHash("sha256").update(bytes).digest("hex") !== digest) {
    throw new Error(`${name}: SHA-256 differs from the recorded artifact`);
  }
  return bytes;
}

function decimal(word) {
  const bytes = Buffer.alloc(8);
  bytes.writeBigUInt64LE(word);
  const value = bytes.readDoubleLE();
  if (!Number.isFinite(value)) throw new Error("Inference returned a nonfinite logit");
  return value;
}

function runInference(tokens, { checkpointPath, bound = 10 } = {}) {
  if (!Array.isArray(tokens) || tokens.length !== 4 ||
      tokens.some(token => !Number.isInteger(token) || token < 0 || token > 255)) {
    throw new Error("Input must contain exactly four byte tokens in [0, 255]");
  }
  if (typeof bound !== "number" || !Number.isFinite(bound)) {
    throw new Error("Bound must be a finite decimal number");
  }
  const manifest = JSON.parse(fs.readFileSync(path.join(directory, "manifest.json"), "utf8"));
  const artifact = manifest.checked;
  checkedFile(artifact.file, artifact.sha256);
  const checkpointBytes = checkpointPath ? fs.readFileSync(checkpointPath) :
    checkedFile("checkpoint.json", manifest.checkpoint_sha256);
  const checkpoint = JSON.parse(checkpointBytes);
  const words = names.flatMap(name => checkpoint.weights[name].bits.map(word => {
    if (!/^[0-9A-Fa-f]{16}$/.test(word)) throw new Error(`Invalid weight word in ${name}`);
    return BigInt(`0x${word}`).toString();
  }));
  if (words.length !== 2488) throw new Error("Checkpoint must contain 2,488 weights");
  const boundBytes = Buffer.alloc(8);
  boundBytes.writeDoubleLE(bound);
  const boundWord = boundBytes.readBigUInt64LE();
  const output = runChecked([ensureHost(), "call", path.join(directory, artifact.file),
    artifact.export, "array-u64", `array-u64:${words.join(",")}`, i64Argument(boundWord),
    ...tokens.map(i64Argument)],
    { cwd: root, encoding: "utf8" }).stdout.trim();
  if (!/^\[(?:[0-9]+(?:, [0-9]+)*)?\]$/.test(output)) throw new Error("Invalid Wasmtime result array");
  const logits = output === "[]" ? [] : output.slice(1, -1).split(", ").map(BigInt);
  if (![0, 256].includes(logits.length) || logits.some(word => word > maxUInt64)) {
    throw new Error("Inference must return 256 binary64 words or an empty rejection result");
  }
  return { tokens, accepted: logits.length === 256, bound,
    bound_bits: boundWord.toString(16).padStart(16, "0"),
    logits_bits: logits.map(word => word.toString(16).padStart(16, "0")),
    logits: logits.map(decimal), verification: artifact.verification,
    wasm_sha256: artifact.sha256,
    checkpoint_sha256: crypto.createHash("sha256").update(checkpointBytes).digest("hex") };
}

function main(args) {
  let tokens;
  const options = {};
  const usage = "usage: tools/tiny-gpt2.js [--checkpoint FILE] [--bound B] " +
    "--text TEXT (four UTF-8 bytes) | --tokens T0 T1 T2 T3";
  if (args.length === 1 && args[0] === "--help") {
    process.stdout.write(`${usage}\n`);
    return;
  }
  for (let i = 0; i < args.length; i++) {
    const option = args[i];
    if (option === "--text" && !tokens && i + 1 < args.length) {
      tokens = [...Buffer.from(args[++i], "utf8")];
    } else if (option === "--tokens" && !tokens && i + 4 < args.length &&
        args.slice(i + 1, i + 5).every(x => /^\d+$/.test(x))) {
      tokens = args.slice(i + 1, i + 5).map(Number);
      i += 4;
    } else if (option === "--checkpoint" && options.checkpointPath === undefined && i + 1 < args.length) {
      options.checkpointPath = args[++i];
    } else if (option === "--bound" && options.bound === undefined && i + 1 < args.length &&
        /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(args[i + 1])) {
      options.bound = Number(args[++i]);
    } else throw new Error(usage);
  }
  if (!tokens) throw new Error(usage);
  process.stdout.write(`${JSON.stringify(runInference(tokens, options))}\n`);
}

if (require.main === module) {
  try { main(process.argv.slice(2)); }
  catch (error) { process.stderr.write(`tiny-gpt2: ${error.message}\n`); process.exitCode = 1; }
}

module.exports = { runInference };
