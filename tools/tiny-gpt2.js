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

function runInference(tokens) {
  if (!Array.isArray(tokens) || tokens.length !== 4 ||
      tokens.some(token => !Number.isInteger(token) || token < 0 || token > 255)) {
    throw new Error("Input must contain exactly four byte tokens in [0, 255]");
  }
  const manifest = JSON.parse(fs.readFileSync(path.join(directory, "manifest.json"), "utf8"));
  checkedFile("inference.wasm", manifest.wasm_sha256);
  const checkpoint = JSON.parse(checkedFile("checkpoint.json", manifest.checkpoint_sha256));
  const words = names.flatMap(name => checkpoint.weights[name].bits.map(word => {
    if (!/^[0-9A-Fa-f]{16}$/.test(word)) throw new Error(`Invalid weight word in ${name}`);
    return BigInt(`0x${word}`).toString();
  }));
  if (words.length !== 2488) throw new Error("Checkpoint must contain 2,488 weights");
  const output = runChecked([ensureHost(), "call", path.join(directory, "inference.wasm"),
    "infer", "array-u64", `array-u64:${words.join(",")}`, ...tokens.map(i64Argument)],
    { cwd: root, encoding: "utf8" }).stdout.trim();
  if (!/^\[[0-9]+(?:, [0-9]+)*\]$/.test(output)) throw new Error("Invalid Wasmtime result array");
  const logits = output.slice(1, -1).split(", ").map(BigInt);
  if (logits.length !== 256 || logits.some(word => word > maxUInt64)) {
    throw new Error("Inference must return 256 binary64 words");
  }
  return { tokens, logits_bits: logits.map(word => word.toString(16).padStart(16, "0")),
    logits: logits.map(decimal), verification: manifest.verification,
    wasm_sha256: manifest.wasm_sha256, checkpoint_sha256: manifest.checkpoint_sha256 };
}

function main(args) {
  let tokens;
  if (args.length === 2 && args[0] === "--text") {
    tokens = [...Buffer.from(args[1], "utf8")];
  } else if (args.length === 5 && args[0] === "--tokens" && args.slice(1).every(x => /^\d+$/.test(x))) {
    tokens = args.slice(1).map(Number);
  } else {
    throw new Error("usage: tools/tiny-gpt2.js --text TEXT (four UTF-8 bytes) | --tokens T0 T1 T2 T3");
  }
  process.stdout.write(`${JSON.stringify(runInference(tokens))}\n`);
}

if (require.main === module) {
  try { main(process.argv.slice(2)); }
  catch (error) { process.stderr.write(`tiny-gpt2: ${error.message}\n`); process.exitCode = 1; }
}

module.exports = { runInference };
