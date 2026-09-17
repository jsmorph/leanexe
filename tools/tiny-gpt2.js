#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { runChecked } = require("./run-process");
const { ensureHost, i64Argument, maxUInt64 } = require("./wasmtime-host");
const { runPrng } = require("./prng");

const root = path.resolve(__dirname, "..");
const names = ["token", "position", "query", "key", "value", "attention", "attention_bias",
  "expand", "expand_bias", "contract", "contract_bias", "head", "head_bias",
  "norm1_scale", "norm1_bias", "norm2_scale", "norm2_bias", "norm_final_scale", "norm_final_bias"];

function checkedFile(directory, name, digest) {
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

function checkTokens(tokens, context) {
  if (!Array.isArray(tokens) || tokens.length === 0 || tokens.length > context ||
      (context === 4 && tokens.length !== 4) ||
      tokens.some(token => !Number.isInteger(token) || token < 0 || token > 255)) {
    throw new Error(context === 4 ? "Input must contain exactly four byte tokens in [0, 255]" :
      "Input must contain 1 to 128 byte tokens in [0, 255]");
  }
}

function createInference({ checkpointPath, bound = 10, context = 4 } = {}) {
  if (![4, 128].includes(context)) throw new Error("Context must be 4 or 128");
  const directory = path.join(root, context === 4 ? "data/tiny-gpt2-v1" : "data/tiny-gpt2-128-v1");
  if (typeof bound !== "number" || !Number.isFinite(bound)) {
    throw new Error("Bound must be a finite decimal number");
  }
  const manifest = JSON.parse(fs.readFileSync(path.join(directory, "manifest.json"), "utf8"));
  const artifact = manifest.checked;
  checkedFile(directory, artifact.file, artifact.sha256);
  const checkpointBytes = checkpointPath ? fs.readFileSync(checkpointPath) :
    checkedFile(directory, "checkpoint.json", manifest.checkpoint_sha256);
  const checkpoint = JSON.parse(checkpointBytes);
  if (checkpoint.architecture.context !== context) throw new Error("Checkpoint context differs from --context");
  const words = names.flatMap(name => checkpoint.weights[name].bits.map(word => {
    if (!/^[0-9A-Fa-f]{16}$/.test(word)) throw new Error(`Invalid weight word in ${name}`);
    return BigInt(`0x${word}`).toString();
  }));
  const weightCount = context === 4 ? 2488 : 2984;
  if (words.length !== weightCount) throw new Error(`Checkpoint must contain ${weightCount} weights`);
  const boundBytes = Buffer.alloc(8);
  boundBytes.writeDoubleLE(bound);
  const boundWord = boundBytes.readBigUInt64LE();
  const command = [ensureHost(), "call", path.join(directory, artifact.file),
    artifact.export, "array-u64", `array-u64:${words.join(",")}`, i64Argument(boundWord)];
  const metadata = { context, bound,
    bound_bits: boundWord.toString(16).padStart(16, "0"),
    verification: artifact.verification,
    wasm_sha256: artifact.sha256,
    checkpoint_sha256: crypto.createHash("sha256").update(checkpointBytes).digest("hex") };
  return tokens => {
    checkTokens(tokens, context);
    const arguments_ = context === 4 ? tokens.map(i64Argument) : [`array-u64:${tokens.join(",")}`];
    const output = runChecked([...command, ...arguments_],
      { cwd: root, encoding: "utf8", timeout: 60000 }).stdout.trim();
    if (!/^\[(?:[0-9]+(?:, [0-9]+)*)?\]$/.test(output)) throw new Error("Invalid Wasmtime result array");
    const logits = output === "[]" ? [] : output.slice(1, -1).split(", ").map(BigInt);
    if (![0, 256].includes(logits.length) || logits.some(word => word > maxUInt64)) {
      throw new Error("Inference must return 256 binary64 words or an empty rejection result");
    }
    return { ...metadata, tokens, accepted: logits.length === 256,
      logits_bits: logits.map(word => word.toString(16).padStart(16, "0")), logits: logits.map(decimal) };
  };
}

function runInference(tokens, options) {
  return createInference(options)(tokens);
}

function sample(logits, topK, temperature, random) {
  const ranked = logits.map((score, token) => ({ score, token }))
    .sort((a, b) => b.score - a.score || a.token - b.token).slice(0, topK);
  const masses = ranked.map(x => Math.exp((x.score - ranked[0].score) / temperature));
  let threshold = random * masses.reduce((sum, mass) => sum + mass, 0);
  for (let i = 0; i < ranked.length; i++) {
    threshold -= masses[i];
    if (threshold < 0) return ranked[i].token;
  }
  return ranked.at(-1).token;
}

function runGeneration(prompt, options = {}) {
  const { context = 4, generate, topK = 40, temperature = 0.8, seed = "42" } = options;
  checkTokens(prompt, context);
  if (!Number.isSafeInteger(generate) || generate < 0) throw new Error("--generate must be a nonnegative integer");
  if (!Number.isInteger(topK) || topK < 1 || topK > 256) throw new Error("--top-k must be an integer in [1, 256]");
  if (!Number.isFinite(temperature) || temperature <= 0) throw new Error("--temperature must be positive and finite");
  if (!/^[0-9]+$/.test(seed) || BigInt(seed) > maxUInt64) throw new Error("--seed must be a UInt64 decimal integer");
  const infer = createInference(options);
  const random = topK === 1 || generate === 0 ? [] : runPrng(seed, String(generate), "9007199254740992");
  const tokens = [...prompt];
  let result = infer(tokens);
  if (!result.accepted) throw new Error("WASM rejected the supplied weights or bound");
  for (let i = 0; i < generate; i++) {
    if (i > 0) result = infer(tokens.slice(-context));
    if (!result.accepted) throw new Error("WASM rejected an inference call during generation");
    tokens.push(sample(result.logits, topK, temperature,
      topK === 1 ? 0 : Number(random[i]) / 9007199254740992));
  }
  return { prompt: Buffer.from(prompt).toString("utf8"), prompt_tokens: prompt,
    completion: Buffer.from(tokens.slice(prompt.length)).toString("utf8"),
    generated_tokens: tokens.slice(prompt.length), tokens, context,
    sampling: { seed, top_k: topK, temperature, count: generate,
      prng: topK === 1 ? null : "Lean SplitMix64 WASM" },
    bound: result.bound, wasm_sha256: result.wasm_sha256, checkpoint_sha256: result.checkpoint_sha256,
    inference_verification: result.verification };
}

function main(args) {
  let tokens;
  const options = {};
  let json = false;
  const usage = "usage: tools/tiny-gpt2.js [--context 4|128] [--checkpoint FILE] [--bound B] " +
    "(--text TEXT | --tokens N ...) [--generate N [--seed N] [--top-k K] [--temperature T] [--json]]\n" +
    "Context 4 requires four UTF-8 bytes; context 128 accepts 1 to 128.\n" +
    "Without --generate, prints all logits as JSON. Generation prints the prompt and completion.\n" +
    "Defaults: context 4, bound 10, seed 42, top-k 40, temperature 0.8.";
  if (args.length === 1 && args[0] === "--help") {
    process.stdout.write(`${usage}\n`);
    return;
  }
  for (let i = 0; i < args.length; i++) {
    const option = args[i];
    if (option === "--text" && !tokens && i + 1 < args.length) {
      tokens = [...Buffer.from(args[++i], "utf8")];
    } else if (option === "--tokens" && !tokens && /^\d+$/.test(args[i + 1] || "")) {
      tokens = [];
      while (i + 1 < args.length && /^\d+$/.test(args[i + 1])) tokens.push(Number(args[++i]));
    } else if (option === "--checkpoint" && options.checkpointPath === undefined && i + 1 < args.length) {
      options.checkpointPath = args[++i];
    } else if (option === "--bound" && options.bound === undefined && i + 1 < args.length &&
        /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(args[i + 1])) {
      options.bound = Number(args[++i]);
    } else if (["--context", "--generate", "--top-k", "--temperature", "--seed"].includes(option) &&
        i + 1 < args.length) {
      const name = { "--context": "context", "--generate": "generate", "--top-k": "topK",
        "--temperature": "temperature", "--seed": "seed" }[option];
      if (options[name] !== undefined) throw new Error(usage);
      const value = args[++i];
      if (!/^(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(value)) throw new Error(usage);
      options[name] = name === "seed" ? value : Number(value);
    } else if (option === "--json" && !json) json = true;
    else throw new Error(usage);
  }
  if (!tokens) throw new Error(usage);
  if (options.generate === undefined) {
    if (options.topK !== undefined || options.temperature !== undefined || options.seed !== undefined) {
      throw new Error("Sampling options require --generate");
    }
    process.stdout.write(`${JSON.stringify(runInference(tokens, options))}\n`);
  } else {
    const result = runGeneration(tokens, options);
    if (json) process.stdout.write(`${JSON.stringify(result)}\n`);
    else {
      process.stdout.write(Buffer.from(result.tokens));
      process.stdout.write("\n");
    }
  }
}

if (require.main === module) {
  try { main(process.argv.slice(2)); }
  catch (error) { process.stderr.write(`tiny-gpt2: ${error.message}\n`); process.exitCode = 1; }
}

module.exports = { runInference, runGeneration };
