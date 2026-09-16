#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");

const root = path.resolve(__dirname, "..");
const source = path.join(root, "data/tiny-gpt2-v1/checkpoint.json");
const target = path.join(root, "proofs/talos/lean/Project/TinyGpt2/CheckpointWords.lean");
const names = ["token", "position", "query", "key", "value", "attention", "attention_bias",
  "expand", "expand_bias", "contract", "contract_bias", "head", "head_bias",
  "norm1_scale", "norm1_bias", "norm2_scale", "norm2_bias", "norm_final_scale", "norm_final_bias"];

function main(mode) {
  if (mode !== "--write" && mode !== "--check") {
    throw new Error("usage: tools/tiny-gpt2-certificate.js --write | --check");
  }
  const bytes = fs.readFileSync(source);
  const manifest = JSON.parse(fs.readFileSync(path.join(root, "data/tiny-gpt2-v1/manifest.json")));
  if (crypto.createHash("sha256").update(bytes).digest("hex") !== manifest.checkpoint_sha256) {
    throw new Error("Checkpoint SHA-256 differs from the manifest");
  }
  const checkpoint = JSON.parse(bytes);
  const words = names.flatMap(name => checkpoint.weights[name].bits.map(word => {
    if (!/^[0-9A-Fa-f]{16}$/.test(word)) throw new Error(`Invalid weight word in ${name}`);
    return `0x${word.toUpperCase()}`;
  }));
  if (words.length !== 2488) throw new Error("Checkpoint must contain 2,488 weights");
  const rows = [];
  for (let i = 0; i < words.length; i += 4) rows.push(`    ${words.slice(i, i + 4).join(", ")}`);
  const result = `import Interpreter.Wasm.IEEE64

namespace Project.TinyGpt2.Checkpoint

set_option maxRecDepth 32768

def words : Array UInt64 :=
  #[
${rows.join(",\n")}
  ]

theorem words_size : words.size = 2488 := by rfl

end Project.TinyGpt2.Checkpoint
`;
  if (mode === "--write") fs.writeFileSync(target, result);
  else if (fs.readFileSync(target, "utf8") !== result) {
    throw new Error("CheckpointWords.lean differs from the checkpoint");
  }
  process.stdout.write(`Checkpoint words ${mode === "--write" ? "written" : "checked"}: ${words.length}\n`);
}

try { main(process.argv.length === 3 ? process.argv[2] : null); }
catch (error) {
  process.stderr.write(`tiny-gpt2-certificate: ${error.message}\n`);
  process.exitCode = 1;
}
