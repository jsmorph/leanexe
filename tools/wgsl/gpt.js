"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { lean, audit } = require("./package");
const { checkBundle } = require("./bundle");
const { execute } = require("./gpt-runtime");
const root = path.resolve(__dirname, "../..");
const proofRoot = path.join(root, "proofs/talos/lean");
const write = (file, bytes) => fs.writeFileSync(file, bytes, { flag: "wx" });
const writeJson = (file, data) => write(file, JSON.stringify(data, null, 2) + "\n");
const digest = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const requireThat = (ok, message) => { if (!ok) throw new Error(message); };
const gptNames = ["GptHiddenArtifact.interface", "GptHiddenArtifact.exact", "GptBundle.artifact", "FinishBinary.artifact_exact",
  "GptHead.restricted_exact", "GptHeadCheckpoint.real_error_uniform"].map(name => `Project.WGSL.${name}`);

async function checkGpt(directory) {
  const checked = await checkBundle(directory);
  try {
    const snapshots = {};
    for (const [name, max] of [["hidden.wasm", 32768], ["finish.wasm", 1024], ["weights.bin", 2488 * 8]]) {
      const data = fs.readFileSync(path.join(checked.directory, name));
      requireThat(data.length <= max, `${name} exceeds its size limit`);
      write(path.join(checked.attempt, name), data);
      snapshots[name] = data;
    }
    await lean("GPT artifact proof dependencies", ["lake", "-d", proofRoot, "build", "Project.WGSL.GptBundle"],
      path.join(checked.attempt, "gpt-dependencies.log"));
    const output = await lean("GPT exact artifacts and checkpoint", ["lake", "-d", proofRoot, "env", "lean", "--run",
      path.join(__dirname, "GptCheck.lean"), "--check", ...Object.keys(snapshots).map(name => path.join(checked.attempt, name))],
    path.join(checked.attempt, "gpt-verify.log"));
    const axioms = audit(output, gptNames);
    requireThat(output.split("\n").filter(line => line === "WGSL_GPT_ARTIFACTS_VERIFIED").length === 1,
      "missing exact GPT artifact verification marker");
    const proof = path.join(checked.attempt, "GptPackageProof.lean");
    write(proof, "import Project.WGSL.GptBundle\n" + fs.readFileSync(path.join(checked.attempt, "Proof.lean"), "utf8") +
      "\ntheorem checkedGptShape : CheckedWGSLPackage.package.kernel.ast.config = Project.WGSL.GptHead.config := by rfl\n" +
      "def checkedGptExecution := @Project.WGSL.GptBundle.artifact _ _ CheckedWGSLPackage.package checkedGptShape\n" +
      "#print axioms checkedGptShape\n#print axioms checkedGptExecution\n");
    const bound = await lean("bind the exact shader to the complete GPT theorem", ["lake", "-d", proofRoot, "env",
      "lean", "--run", proof, checked.shaderPath, checked.manifestPath], path.join(checked.attempt, "gpt-package-verify.log"));
    const composedAxioms = audit(bound, ["package", "artifact", "numerical", "numericalWide", "exact"]
      .map(name => `CheckedWGSLPackage.${name}`).concat(["checkedGptShape", "checkedGptExecution"]));
    for (const [name, data] of Object.entries(snapshots))
      requireThat(data.equals(fs.readFileSync(path.join(checked.attempt, name))), `${name} snapshot changed during verification`);
    const receipt = { ...checked.receipt, subject: "Checkpoint GPT hidden Wasm, GEMM bridge, selected WGSL head and bias-addition Wasm",
      artifacts: Object.fromEntries(Object.entries(snapshots).map(([name, data]) => [name, { sha256: digest(data), bytes: data.length }])),
      gptAxioms: axioms, gptCompositionAxioms: composedAxioms,
      gptProofSha256: digest(fs.readFileSync(proof)),
      inputDomain: "four byte tokens; fixed 2488-word checkpoint; last context position",
      numericalBound: "1/10000 + 16*TinyGpt2.ErrorBudget.hidden(4, sqrt(1/100000), sqrt(1/100000), sqrt(1/100000))",
      numericalLimitation: "The uniform worst-case bound is extremely loose (approximately 4.85e9); it is not a tight accuracy certificate.",
      headErrorBound: "1/10000 against the real head applied to the computed binary64 hidden row",
      conversionContract: "Native binary64-to-binary32 and binary32-to-binary64 conversions match Precision.demote/promote on finite inputs; transfers satisfy GptHeadHost.Inputs.",
      executionBoundary: "Native orchestration calls the three proved Wasm artifacts and the independently checked WGSL artifact; native engines and conversions are explicit conformance assumptions." };
    writeJson(path.join(checked.attempt, "gpt-verification.json"), receipt);
    console.log(`GPT bundle verified: ${checked.attempt}`);
    return { ...checked, hiddenBytes: snapshots["hidden.wasm"], finishBytes: snapshots["finish.wasm"],
      weightsBytes: snapshots["weights.bin"], receipt };
  } catch (error) {
    writeJson(path.join(checked.attempt, "gpt-failure.json"), { status: "error", error: error.message });
    throw error;
  }
}

async function generate(directory) {
  directory = path.resolve(directory);
  fs.mkdirSync(path.dirname(directory), { recursive: true });
  fs.mkdirSync(directory);
  await lean("generate the selected Lean GPT head", ["lake", "-d", proofRoot, "env", "lean", "--run",
    path.join(__dirname, "GptHeadGenerate.lean"), directory], path.join(directory, "generate.log"));
  await lean("emit the checked GPT Wasm and checkpoint", ["lake", "-d", proofRoot, "env", "lean", "--run",
    path.join(__dirname, "GptCheck.lean"), "--emit", directory], path.join(directory, "emit.log"));
  fs.copyFileSync(path.join(root, "test/wgsl/host/host.wasm"), path.join(directory, "host.wasm"), fs.constants.COPYFILE_EXCL);
  return directory;
}

async function corpus(directory) {
  directory = path.resolve(directory);
  fs.mkdirSync(path.dirname(directory), { recursive: true });
  fs.mkdirSync(directory);
  const cases = JSON.parse(fs.readFileSync(path.join(__dirname, "gpt-corpus.json"), "utf8"));
  const bundle = path.join(directory, "bundle");
  await generate(bundle);
  const checked = await checkGpt(bundle);
  const results = [];
  for (const item of cases.positive) {
    const result = await run(checked, item.tokens, item.name);
    results.push({ name: item.name, status: result.status,
      evidence: path.join(checked.attempt, `gpt-${item.name}.json`) });
  }
  // Exercise the same exact-byte gate with one altered input at a time. The
  // independently verified shader and host are shared by the positive cases.
  for (const item of cases.negative) {
    const altered = path.join(directory, item.name);
    fs.mkdirSync(altered);
    for (const name of ["hidden.wasm", "finish.wasm", "weights.bin"]) {
      const bytes = fs.readFileSync(path.join(checked.attempt, name));
      if (name === item.file) bytes[item.offset] ^= item.xor;
      write(path.join(altered, name), bytes);
    }
    const log = path.join(altered, "verify.log");
    let failed = false;
    try {
      await lean("reject altered GPT artifact", ["lake", "-d", proofRoot, "env", "lean", "--run",
        path.join(__dirname, "GptCheck.lean"), "--check",
        ...["hidden.wasm", "finish.wasm", "weights.bin"].map(name => path.join(altered, name))], log);
    } catch (error) {
      failed = true;
    }
    requireThat(failed && fs.readFileSync(log, "utf8").includes(item.failure),
      `negative GPT case ${item.name} did not fail for the expected reason`);
    results.push({ name: item.name, status: "rejected", diagnostics: log });
  }
  writeJson(path.join(directory, "corpus.json"), { status: "pass",
    verification: path.join(checked.attempt, "gpt-verification.json"), results });
  console.log(`GPT corpus passed: ${results.length} cases; ${directory}`);
}

async function run(checked, tokens, label, dispatch) {
  requireThat(tokens.length === 4 && tokens.every(token => Number.isInteger(token) && token >= 0 && token < 256), "expected four byte tokens");
  const output = await lean("pure Lean mixed-precision reference", ["lake", "-d", proofRoot, "env", "lean", "--run",
    path.join(__dirname, "GptModel.lean"), ...tokens.map(String)], path.join(checked.attempt, `gpt-${label}-reference.log`));
  const lines = output.split("\n").filter(line => line.startsWith("{"));
  requireThat(lines.length === 1, "missing or duplicate Lean reference output");
  const reference = JSON.parse(lines[0]);
  writeJson(path.join(checked.attempt, `gpt-${label}-reference.json`), reference);
  const result = execute(checked, tokens, reference, label, dispatch);
  console.log(`GPT Wasm → WGSL → Wasm passed: ${result.checkedElements} logits; ${checked.attempt}/gpt-${label}.json`);
  return result;
}

async function session(checked, inputs) {
  const { NativeSession } = require("./native-session");
  const bytes = Buffer.alloc(4);
  const weights = Array.from({ length: 1024 }, (_, i) => {
    bytes.writeFloatLE(checked.weightsBytes.readDoubleLE(8 * (1184 + i)));
    return bytes.readUInt32LE();
  });
  const native = new NativeSession(checked, weights, path.join(checked.attempt, "gpt-session-native.log"));
  const results = [];
  try {
    for (const [i, tokens] of inputs.entries())
      results.push(await run(checked, tokens, `session-${i}`, values => native.dispatch(values)));
    const last = results.at(-1).residency;
    requireThat(last?.weightUploads === 1 && last.pipelineCreations === 1 && last.dispatches === inputs.length,
      "native session did not retain one weight buffer and pipeline");
    requireThat(Number.isFinite(last.nativeStartupMs) && last.nativeStartupMs > 0,
      "native session did not report its startup cost");
    // A changed Wasm B snapshot must never be dispatched against resident B.
    const changed = weights.slice();
    changed[0] ^= 1;
    let rejected = false;
    try { native.dispatch({ a: [0, 0, 0, 0], b: changed }); }
    catch (error) { rejected = error.message.includes("resident weights differ"); }
    requireThat(rejected, "changed resident weight snapshot was not rejected");
  } finally {
    await native.close();
  }
  writeJson(path.join(checked.attempt, "gpt-session.json"), { status: "pass", inputs,
    checkedElements: 256 * inputs.length, changedWeightsRejected: true,
    residency: results.at(-1).residency, elapsedMs: results.map(result => result.elapsedMs),
    nativeClosed: true, universalRuntimeConformanceEstablished: false });
  console.log(`Resident GPT session passed: ${inputs.length} inputs; ${checked.attempt}/gpt-session.json`);
}

async function main([command, directory, ...rest]) {
  if (command === "wgsl-gpt-build") {
    requireThat(rest.length === 0, "unexpected arguments");
    await generate(directory);
    await run(await checkGpt(directory), [76, 101, 97, 110], "lean");
  } else if (command === "wgsl-gpt-check") {
    requireThat(rest.length === 0, "unexpected arguments");
    await checkGpt(directory);
  } else if (command === "wgsl-gpt-run") {
    requireThat(rest.length === 4 && rest.every(s => /^(0|[1-9][0-9]*)$/.test(s)), "expected four byte tokens");
    const tokens = rest.map(Number);
    requireThat(tokens.every(t => t < 256), "token exceeds byte range");
    await run(await checkGpt(directory), tokens, "input");
  } else if (command === "wgsl-gpt-corpus") {
    requireThat(rest.length === 0, "unexpected arguments");
    await corpus(directory);
  } else if (command === "wgsl-gpt-benchmark") {
    requireThat(rest.length === 1, "expected an existing GPT bundle and fresh benchmark directory");
    await require("./benchmark").main(directory, rest[0]);
  } else if (command === "wgsl-gpt-session") {
    requireThat(rest.length >= 4 && rest.length <= 64 && rest.length % 4 === 0 &&
      rest.every(s => /^(0|[1-9][0-9]*)$/.test(s) && Number(s) < 256),
    "expected 1–16 groups of four byte tokens");
    const inputs = [];
    for (let i = 0; i < rest.length; i += 4) inputs.push(rest.slice(i, i + 4).map(Number));
    await session(await checkGpt(directory), inputs);
  } else throw new Error(`unknown GPT command: ${command}`);
}
module.exports = { main, generate, checkGpt, run, corpus, session };
