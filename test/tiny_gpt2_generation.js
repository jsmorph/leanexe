#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runInference, runGeneration } = require("../tools/tiny-gpt2");
const { runChecked, spawnResult } = require("../tools/run-process");

const root = path.resolve(__dirname, "..");
const cli = path.join(root, "tools/tiny-gpt2.js");
const samples = JSON.parse(fs.readFileSync(path.join(root, "data/tiny-gpt2-128-v1/completions.json")));
for (const sample of samples.samples) {
  const result = runGeneration([...Buffer.from(sample.prompt)], { context: 128,
    generate: sample.count, seed: String(sample.seed), topK: sample.top_k, temperature: sample.temperature });
  assert.equal(result.completion, sample.completion);
  assert.deepEqual(result.generated_tokens, sample.tokens);
  assert.equal(result.wasm_sha256, samples.wasm_sha256);
  assert.equal(result.checkpoint_sha256, samples.checkpoint_sha256);
}

const prompt = Array(128).fill(97);
const greedy = runGeneration(prompt, { context: 128, generate: 2, topK: 1 });
const rolled = runInference([...prompt.slice(1), greedy.generated_tokens[0]], { context: 128 });
assert.equal(greedy.generated_tokens[1], rolled.logits.indexOf(Math.max(...rolled.logits)));
const output = runChecked([cli, "--context", "128", "--text", "ROMEO:",
  "--generate", "2", "--top-k", "1", "--json"], { cwd: root, encoding: "utf8" }).stdout;
const parsed = JSON.parse(output);
assert.equal(parsed.generated_tokens.length, 2);
assert.equal(parsed.prompt, "ROMEO:");
const text = runChecked([cli, "--context", "128", "--text", "ROMEO:",
  "--generate", "2", "--top-k", "1"], { cwd: root, encoding: "utf8" }).stdout;
assert.equal(text, Buffer.from(parsed.tokens).toString("utf8") + "\n");
for (const args of [["--text", ""], ["--text", "a".repeat(129)],
  ["--text", "a", "--generate", "1", "--temperature", "0"],
  ["--text", "a", "--generate", "1", "--top-k", "257"]]) {
  const result = spawnResult([cli, "--context", "128", ...args], { cwd: root, encoding: "utf8" });
  assert.equal(result.status, 1);
  assert.equal(result.stdout, "");
  assert.match(result.stderr, /^tiny-gpt2:/);
}
const original = runInference([84, 111, 32, 98]);
assert.equal(original.context, 4);
assert.equal(original.accepted, true);
assert.equal(original.logits.length, 256);
process.stdout.write("Checked three seeded completions, rolling context, CLI text/JSON, rejection, and GPT-2/4\n");
