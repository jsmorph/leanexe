#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { callI64Slots } = require("./wasmtime-host");

const root = path.resolve(__dirname, "..");

function parseWord(value, field) {
  if (typeof value !== "string" || !/^[0-9a-fA-F]{16}$/.test(value)) {
    throw new Error(`${field} must be a 16-digit hexadecimal string`);
  }
  return BigInt(`0x${value}`);
}

function decimal(word) {
  const bytes = Buffer.alloc(8);
  bytes.writeBigUInt64LE(word);
  return bytes.readDoubleLE();
}

function inputWords(demo, input) {
  if (demo.kind === "layernorm") {
    return demo.fields.flatMap(field => {
      if (!Array.isArray(input[field]) || input[field].length !== 4) {
        throw new Error(`${field} must contain exactly four binary64 words`);
      }
      return input[field].map((word, i) => parseWord(word, `${field}[${i}]`));
    });
  }
  if (demo.kind === "softmax") {
    if (!Array.isArray(input.scores_bits) || input.scores_bits.length < 1 || input.scores_bits.length > 4) {
      throw new Error("scores_bits must contain one to four binary64 words");
    }
    const scores = input.scores_bits.map((word, i) => parseWord(word, `scores_bits[${i}]`));
    return [BigInt(scores.length), ...scores, ...Array(4 - scores.length).fill(0n)];
  }
  return demo.fields.map(field => parseWord(input[field], field));
}

function runDemo(name, input) {
  const manifest = JSON.parse(fs.readFileSync(path.join(root, "data/numerical/manifest.json"), "utf8"));
  const demo = manifest.demos.find(item => item.name === name);
  if (!demo) throw new Error(`unknown numerical demo: ${name}`);
  if (!input || typeof input !== "object" || Array.isArray(input) ||
      Object.keys(input).sort().join(",") !== [...demo.fields].sort().join(",")) {
    throw new Error(`${name} requires fields: ${demo.fields.join(", ")}`);
  }
  const arguments_ = inputWords(demo, input);
  const wasm = path.join(root, demo.wasm);
  const digest = crypto.createHash("sha256").update(fs.readFileSync(wasm)).digest("hex");
  if (digest !== demo.sha256) throw new Error(`${name}: WASM digest differs from the recorded demonstration`);
  const [status, ...words] = callI64Slots(wasm, demo.export, demo.kind ? 5 : 2, arguments_);
  if (status !== 0n && status !== 1n) throw new Error(`${name}: unexpected status ${status}`);
  const hex = words.map(word => word.toString(16).padStart(16, "0"));
  const result = demo.kind === "softmax"
    ? { status: Number(status), active: Number(arguments_[0]), probabilities_bits: hex }
    : demo.kind === "layernorm"
      ? { status: Number(status), values_bits: hex }
      : { status: Number(status), bits: hex[0] };
  if (status === 0n) {
    const values = words.map(decimal);
    if (values.some(value => !Number.isFinite(value))) throw new Error(`${name}: accepted output is nonfinite`);
    Object.assign(result, demo.kind === "softmax"
      ? { probabilities: values, normalization_error_bound: demo.normalizationErrorBound }
      : demo.kind === "layernorm" ? { values } : { value: values[0] });
    Object.assign(result, { absolute_error_bound: demo.absoluteErrorBound,
      theorem: demo.theorem, wasm_sha256: digest });
  }
  return result;
}

function decimalWord(text) {
  if (!/^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(text)) {
    throw new Error(`invalid decimal input: ${text}`);
  }
  const value = Number(text);
  if (!Number.isFinite(value)) throw new Error(`nonfinite decimal input: ${text}`);
  const bytes = Buffer.alloc(8);
  bytes.writeDoubleLE(value);
  return bytes.readBigUInt64LE().toString(16).padStart(16, "0");
}

function main(args) {
  let input;
  if (args[0] === "gelu" && args[1] === "--value" && args.length === 3) {
    input = { x_bits: decimalWord(args[2]) };
  } else if (args[0] === "softmax" && args[1] === "--scores" && args.length >= 3 && args.length <= 6) {
    input = { scores_bits: args.slice(2).map(decimalWord) };
  } else if (args[0] === "layernorm" && args[1] === "--values" &&
      (args.length === 6 || (args.length === 16 && args[6] === "--scale" && args[11] === "--bias"))) {
    input = {
      values_bits: args.slice(2, 6).map(decimalWord),
      scale_bits: (args.length === 6 ? ["1", "1", "1", "1"] : args.slice(7, 11)).map(decimalWord),
      bias_bits: (args.length === 6 ? ["0", "0", "0", "0"] : args.slice(12, 16)).map(decimalWord),
    };
  } else {
    if (args.length !== 1 && !(args.length === 3 && args[1] === "--input")) {
      throw new Error("usage: tools/numeric-demo.js <demo> [--input FILE], gelu --value X, softmax --scores SCORE [SCORE ...], or layernorm --values X0 X1 X2 X3 [--scale G0 G1 G2 G3 --bias B0 B1 B2 B3]");
    }
    input = JSON.parse(fs.readFileSync(args.length === 3 ? args[2] : 0, "utf8"));
  }
  process.stdout.write(`${JSON.stringify(runDemo(args[0], input))}\n`);
}

if (require.main === module) {
  try { main(process.argv.slice(2)); }
  catch (error) { process.stderr.write(`numeric-demo: ${error.message}\n`); process.exitCode = 1; }
}

module.exports = { runDemo };
