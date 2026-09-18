"use strict";

// Verify the six delivered shader texts, without generating replacements or
// running an inference implementation. The selected arithmetic profile is a
// theorem premise; this command does not certify a native/browser GPU driver.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { isDeepStrictEqual } = require("node:util");
const { checkPackage, lean, audit } = require("../package");
const root = path.resolve(__dirname, "../../..");
const hash = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const need = (ok, message) => { if (!ok) throw Error(message); };
const write = (file, value) => fs.writeFileSync(file, JSON.stringify(value, null, 2) + "\n", { flag: "wx" });
const shapes = [[768,2304],[768,768],[768,3072],[3072,768],[768,25129],[768,25128]]
  .map(([inner,cols], i) => ({ inner, cols, shader: `kernel-${i}.wgsl` }));
const roles = ["qkv", "attention", "expansion", "projection", "vocabularyLeft", "vocabularyRight"];
const matrixTheorems = ["exact_from_dispatch", "vocabulary_left_layout", "vocabulary_right_layout",
  "vocabulary_from_dispatch", "vocabulary_exact", "layer_shape", "layer_matrix_injective",
  "head_shapes", "fifty_matrices", "attention_input_range", "fusion_from_dispatch", "vocabulary_fusion_choices"]
  .map(n => `Project.Gpt2.Matrix.${n}`).concat(
    ["fusion_iff_choices", "separate_evaluate"].map(n => `Project.WGSL.ArithmeticChoice.${n}`),
    ["separate_word", "fused_word", "both_admitted"].map(n => `ArithmeticRegression.${n}`));

async function check(directory) {
  directory = path.resolve(directory);
  const manifestBytes = fs.readFileSync(path.join(directory, "manifest.json"));
  const manifest = JSON.parse(manifestBytes);
  need(manifest.schemaVersion === 2 && isDeepStrictEqual(manifest.shapes, shapes), "unexpected GPT-2 shader plan");
  const bodyCompiler = manifest.shaderCompiler === "lean-body-wgsl";
  need(bodyCompiler ? manifest.shaderEntryPoint === "lean_kernel" :
    manifest.shaderCompiler === undefined && (manifest.shaderEntryPoint ?? "gemm_f32") === "gemm_f32",
    "unsupported GPT-2 shader compiler or entry point");
  const snapshots = shapes.map(shape => {
    const bytes = fs.readFileSync(path.join(directory, shape.shader));
    need(bytes.length === manifest.sizes[shape.shader] && hash(bytes) === manifest.sha256[shape.shader], `${shape.shader}: bundle identity mismatch`);
    return bytes;
  });
  const parent = path.join(root, "build/gpt2/shader-checks");
  fs.mkdirSync(parent, { recursive: true });
  const attempt = fs.mkdtempSync(path.join(parent, "check-"));
  fs.writeFileSync(path.join(attempt, "bundle-manifest.json"), manifestBytes, { flag: "wx" });
  const results = [];
  let vocabularyVerification = null;
  try {
    const proofRoot = path.join(root, "proofs/talos/lean");
    await lean("GPT-2 matrix proof dependencies", ["lake", "-d", proofRoot, "build", "Project.Gpt2.MatrixArithmetic"],
      path.join(attempt, "matrix-dependencies.log"));
    const matrixOutput = await lean("GPT-2 matrix layout and decomposition", ["lake", "-d", proofRoot, "env", "lean",
      "--run", path.join(__dirname, "CheckMatrix.lean"), path.join(attempt, "bundle-manifest.json")],
      path.join(attempt, "matrix-verify.log"));
    const matrixAxioms = audit(matrixOutput, matrixTheorems);
    need(matrixOutput.split("\n").filter(s => s === "GPT2_MATRIX_PLAN 50").length === 1, "missing checked matrix plan");
    if (bodyCompiler) {
      const checked = await require("./body-shaders").checkExisting(directory, attempt, snapshots);
      results.push(...checked.results);
      vocabularyVerification = checked.vocabulary;
    } else for (const [index, shape] of shapes.entries()) {
      const selected = path.join(attempt, String(index));
      fs.mkdirSync(selected);
      fs.writeFileSync(path.join(selected, "kernel.wgsl"), snapshots[index], { flag: "wx" });
      // Construct the requested semantic contract; the kernel checker must
      // independently establish that every field matches the parsed shader.
      write(path.join(selected, "manifest.json"), {
        schemaVersion: 1, kernel: "gemm_f32", entryPoint: "gemm_f32", wgslRevision: "2026-08-17",
        profile: { id: "leanexe-f32-rne-separate-v1", revision: 1 },
        dimensions: { rows: 1, inner: shape.inner, cols: shape.cols },
        bindings: { group: 0, a: 0, b: 1, c: 2 },
        buffers: Object.fromEntries([["a",shape.inner],["b",shape.inner*shape.cols],["c",shape.cols]]
          .map(([name,elements]) => [name, { elements, bytes: elements*4 }])),
        workgroupSize: [8,8,1], dispatchWorkgroups: [Math.ceil(shape.cols/8),1,1],
      });
      const checked = await checkPackage(selected, { wordsOnly: true, gpt2Shader: roles[index] });
      need(checked.shader.equals(snapshots[index]), "proof identified different shader bytes");
      results.push({ shader: shape.shader, role: roles[index], dimensions: checked.metadata.dimensions,
        shaderSha256: checked.receipt.shaderSha256, verification: path.join(checked.attempt, "verification.json") });
    }
    need(fs.readFileSync(path.join(directory, "manifest.json")).equals(manifestBytes), "bundle manifest changed during checking");
    for (const [index,shape] of shapes.entries())
      need(fs.readFileSync(path.join(directory,shape.shader)).equals(snapshots[index]), "delivered shader changed during checking");
    write(path.join(attempt, "verification.json"), { status: "pass", bundleManifestSha256: hash(manifestBytes),
      subject: bodyCompiler ? "Six delivered WGSL shaders execute their compiled Lean definition bodies and the GPT-2 packed matrix specification" :
        "Six delivered GPT-2 WGSL shaders implement the selected Lean binary32 GEMM",
      shaderCompiler: bodyCompiler ? "lean-body-wgsl" : "fixed-gemm-template",
      profile: "leanexe-f32-rne-separate-v1", numericalErrorTolerance: null,
      runtimeConformanceEstablished: false, modelCompositionEstablished: false,
      matrixAxioms, matrixAssignmentsChecked: 50, vocabularyDecompositionProved: true, vocabularyVerification,
      fusionAlternative: bodyCompiler ? null : "Each output equals the Lean binary32 algorithm for some concrete per-step fused/separate choices",
      scope: "Shader word equality to Lean matrix products, packed layouts, vocabulary decomposition and matrix descriptor plan; no checkpoint contents, float conversions, Wasm, host schedule or driver proof",
      results });
    console.log(`GPT-2 WGSL fidelity: all six shaders verified; ${attempt}`);
    return { attempt, results };
  } catch (error) {
    write(path.join(attempt,"failure.json"), { status: "error", error: error.message, results });
    throw error;
  }
}
async function layoutCorpus(directory) {
  directory = path.resolve(directory);
  fs.mkdirSync(path.dirname(directory), { recursive: true });
  fs.mkdirSync(directory);
  const proofRoot = path.join(root, "proofs/talos/lean");
  await lean("GPT-2 matrix corpus dependencies", ["lake", "-d", proofRoot, "build", "Project.Gpt2.MatrixArithmetic"],
    path.join(directory, "dependencies.log"));
  const results = [];
  for (const item of require("./corpus.json").matrixPlan) {
    const matrices = Array.from({ length: 50 }, (_, i) => ({
      file: `matrix-${String(i).padStart(2, "0")}.bin`, shape: i < 48 ? i % 4 : i - 44 }));
    if (item.shape !== undefined) matrices[item.matrix].shape = item.shape;
    if (item.file !== undefined) matrices[item.matrix].file = item.file;
    if (item.extra) matrices[item.matrix].unchecked = true;
    if (item.dropLast) matrices.pop();
    const manifest = path.join(directory, `${item.name}.json`), log = path.join(directory, `${item.name}.log`);
    write(manifest, { matrices });
    let failure;
    try {
      const output = await lean(`GPT-2 matrix corpus ${item.name}`, ["lake", "-d", proofRoot, "env", "lean",
        "--run", path.join(__dirname, "CheckMatrix.lean"), manifest], log);
      audit(output, matrixTheorems);
    } catch (error) { failure = error.message; }
    if (item.accept) need(!failure, `${item.name}: ${failure}`);
    else need(failure && fs.readFileSync(log, "utf8").includes("GPT-2 matrix assignments differ"),
      `${item.name} did not reject the changed plan as expected`);
    results.push({ name: item.name, status: item.accept ? "pass" : "rejected" });
  }
  write(path.join(directory, "corpus.json"), { status: "pass", results });
  console.log(`GPT-2 matrix corpus passed: ${results.length} cases; ${directory}`);
}
module.exports = { check, layoutCorpus };
