"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { lean, checkPackage } = require("./package");
const { checkGpt, run } = require("./gpt");
const { nativeJob } = require("./wasm-host");
const root = path.resolve(__dirname, "../..");
const writeJson = (file, data) => fs.writeFileSync(file, JSON.stringify(data, null, 2) + "\n", { flag: "wx" });
const requireThat = (ok, message) => { if (!ok) throw new Error(message); };
function word32(value) {
  const bytes = Buffer.alloc(4);
  bytes.writeFloatLE(value);
  return bytes.readUInt32LE();
}
function row32(words) {
  return words.map(word => {
    const bytes = Buffer.alloc(8);
    bytes.writeBigUInt64LE(BigInt(word));
    return word32(bytes.readDoubleLE());
  });
}

async function main(bundle, directory) {
  directory = path.resolve(directory);
  fs.mkdirSync(path.dirname(directory), { recursive: true });
  fs.mkdirSync(directory);
  const config = JSON.parse(fs.readFileSync(path.join(__dirname, "benchmark-corpus.json"), "utf8"));
  const inputs = JSON.parse(fs.readFileSync(path.join(__dirname, "gpt-corpus.json"), "utf8")).positive;
  const gpt = await checkGpt(bundle);
  const executions = [];
  for (const input of inputs) executions.push(await run(gpt, input.tokens, `benchmark-${input.name}`));
  const rows = executions.map(result => row32(result.hidden));
  const weights = Array.from({ length: 1024 }, (_, i) => word32(gpt.weightsBytes.readDoubleLE(8 * (1184 + i))));
  const results = [];
  for (const candidate of config.candidates) {
    const destination = path.join(directory, candidate.name);
    fs.mkdirSync(destination);
    let checked;
    if (candidate.rows === 1 && candidate.workgroup[0] === 8 && candidate.workgroup[1] === 8) {
      checked = gpt;
      for (const name of ["kernel.wgsl", "manifest.json"])
        fs.copyFileSync(path.join(gpt.attempt, name), path.join(destination, name), fs.constants.COPYFILE_EXCL);
    } else {
      await lean("generate the supported head benchmark candidate", ["lake", "env", "lean", "--run",
        path.join(__dirname, "BenchmarkGenerate.lean"), destination, String(candidate.rows),
        ...candidate.workgroup.map(String)], path.join(destination, "generate.log"));
      checked = await checkPackage(destination);
    }
    requireThat(checked.metadata.dimensions.rows === candidate.rows &&
      checked.metadata.dimensions.cols === 256 && checked.metadata.dimensions.inner === 4 &&
      checked.metadata.workgroupSize[0] === candidate.workgroup[0] &&
      checked.metadata.workgroupSize[1] === candidate.workgroup[1], "benchmark candidate shape differs");
    const inputsA = candidate.rows === 1 ? rows : [rows.flat()];
    const job = { wgsl: checked.shader.toString("utf8"), manifest: checked.metadata,
      inputs: { a: inputsA[0], b: weights },
      backend: process.env.WGPU_BACKEND_TYPE || "Vulkan",
      adapter: process.env.LEANEXE_WGPU_ADAPTER || (process.platform === "darwin" ? "SwiftShader" : "llvmpipe"),
      benchmark: { inputsA, repetitions: config.repetitions, warmupRounds: config.warmupRounds } };
    const response = nativeJob(job, path.join(destination, "native.log"));
    requireThat(response.benchmark?.status === "pass", "native benchmark did not pass");
    const report = { ...response, candidate, verification: checked.receipt,
      proofAttempt: checked.attempt, inputTokens: inputs.map(input => input.tokens),
      measurementScope: "vocabulary projection on the recorded CPU WebGPU device; excludes hidden computation and bias Wasm" };
    writeJson(path.join(destination, "evidence.json"), report);
    results.push({ candidate, medianSequenceMs: response.benchmark.medianSequenceMs,
      rowsPerSequence: response.benchmark.rowsPerSequence,
      checkedWords: response.benchmark.checkedWords, evidence: path.join(destination, "evidence.json") });
    console.log(`Head benchmark passed: ${candidate.name}; ${JSON.stringify(response.benchmark.medianSequenceMs)} ms per three inputs`);
  }
  const report = { status: "pass", results, config,
    completeGptEvidence: inputs.map(input => path.join(gpt.attempt, `gpt-benchmark-${input.name}.json`)),
    limitation: "Small CPU-emulation measurements do not predict physical-GPU throughput or prove runtime conformance." };
  writeJson(path.join(directory, "benchmark.json"), report);
  console.log(`Verified head benchmark complete: ${directory}`);
}

module.exports = { main };
